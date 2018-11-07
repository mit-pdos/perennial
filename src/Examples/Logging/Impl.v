Require Import POCS.

Require Export Examples.Logging.TxnDiskAPI.
Require Export Examples.ReplicatedDisk.OneDiskAPI.

From Array Require Import Array.

Import ProcNotations.
Local Open Scope proc.

Module D := OneDisk.
Module TxnD := TxnDisk.

(* disk layout:

| log header (1 block) | descriptor block (1 block) |
| log value region (LOG_LENGTH blocks; see below) | data region |
*)

(* The descriptor block encodes 32-bit addresses; it fits 1024byte/32bits = 256
addresses. *)
Definition LOG_LENGTH: nat := 256.
Opaque LOG_LENGTH.
Definition __log_length_calculation: LOG_LENGTH = blockbytes / 4
  := eq_refl.

Record LogHdr :=
  { committed: bool;
    log_length: nat;
    log_length_ok: log_length <= LOG_LENGTH; }.

Record Descriptor :=
  { addresses: list addr;
    (* TODO: restrict addrs to be < 2^32 for encoding in one block *)
    addresses_length:
      length addresses = LOG_LENGTH; }.

(* We encode the log with two blocks: a header and a descriptor block. The header has a bit which commits the transaction: log_commit first records the transaction completes and then applies it, so that recovery (also log_apply) can see that the transaction is committed and finish applying it. *)

(* The logical log is either:
- a partial list of writes, or
- a committed list of writes.

The partial list of writes is represented by a committed flag of false followed
by [hdr.(log_length)] addresses from the descriptor block (the rest are ignored)
paired with the values in the log region of the disk. The length of the log is
restricted by LogHdr so that there are always enough addresses in the descriptor
block and spaces on disk for the values.

A committed transaction is represented almost the same way, except that the committed flag is set to true.

On crash committed will generally be false, so the logical log is empty and the
whole thing is aborted, reverting the disk to its old state. The one exception
is after writing the commit header but before finishing apply.
 *)

(* Once we have a data region + logical log, we map that to the TxnDiskAPI's two
disks by setting the old disk to the data region and the new disk to the data
region + writes from the logical log. *)

Record block_encoder T :=
  { encode: T -> block;
    decode: block -> T;
    encode_decode: forall (x:T), decode (encode x) = x; }.

Axiom LogHdr_fmt: block_encoder LogHdr.
Axiom Descriptor_fmt: block_encoder Descriptor.

Definition read a := Prim (D.op_read a).
Definition write a v := Prim (D.op_write a v).
Definition size := Prim (D.op_size).

Definition gethdr: proc D.Op LogHdr :=
  b <- read 0;
    Ret (LogHdr_fmt.(decode) b).

Definition writehdr (hdr:LogHdr) :=
  write 0 (LogHdr_fmt.(encode) hdr).

Definition hdr_full (hdr:LogHdr) :
  {hdr.(log_length) = LOG_LENGTH} + {hdr.(log_length) < LOG_LENGTH}.
  destruct (lt_dec (hdr.(log_length)) LOG_LENGTH).
  right; auto.
  pose proof (hdr.(log_length_ok)).
  left; omega.
Qed.

Definition hdr_inc (hdr:LogHdr) (pf:hdr.(log_length) < LOG_LENGTH) : LogHdr.
  refine {| committed := hdr.(committed);
            log_length := hdr.(log_length) + 1; |}.
  abstract omega.
Defined.

Definition empty_hdr : LogHdr.
  refine {| committed := false;
            log_length := 0; |}.
  abstract omega.
Defined.

Definition hdr_setcommit (hdr:LogHdr) : LogHdr :=
  {| committed := true;
     log_length := hdr.(log_length);
     log_length_ok := hdr.(log_length_ok); |}.

Definition getdesc: proc D.Op Descriptor :=
  b <- read 1;
    Ret (Descriptor_fmt.(decode) b).

Definition writedesc (ds:Descriptor) :=
  write 1 (Descriptor_fmt.(encode) ds).

Instance def_desc : Default Descriptor.
  refine {| addresses := List.repeat 0 LOG_LENGTH |}.
  apply repeat_length.
Defined.

Definition add_addr (ds:Descriptor) (idx:nat) (a:addr) : Descriptor.
  refine {| addresses := assign ds.(addresses) idx a; |}.
  rewrite length_assign.
  apply ds.(addresses_length).
Defined.

(* log init establishes that the log and descriptor are valid (note that the
block_encoder does not assume that every block is parseable, only the encodings)
and correspond to an empty log *)
Definition log_init :=
  sz <- size;
    if lt_dec sz (2+LOG_LENGTH) then
      Ret InitFailed
    else
      _ <- writehdr empty_hdr;
    _ <- writedesc default; (* value is unimportant, ignored due to log_length = 0 *)
    Ret Initialized.

Definition log_size :=
  sz <- size;
    (* this subtraction never underflows because of the size established by init
    (and the size is an invariant) *)
    Ret (sz-(2+LOG_LENGTH)).

(* manipulating the log region *)
Definition set_desc desc (i:nat) a v :=
  _ <- writedesc (add_addr desc i a);
    write (2+i) v.

Definition get_logwrite desc (i:nat) :=
    let a := sel desc.(addresses) i in
    v <- read (2+i);
      Ret (a, v).

(* manipulating the data region *)
Definition data_read a :=
  read (2+LOG_LENGTH+a).

Definition data_write a v :=
  write (2+LOG_LENGTH+a) v.

(* reads just go directly to the data region (transactions don't read their own
writes) *)
Definition log_read a :=
  data_read a.

Definition log_write a v :=
  (* I believe out-of-bounds reads at the logical level are always translated to
  out-of-bounds applies when we attempt to apply the log; this works but is
  complicated, since the write does actually take space in the physical log but
  won't do anything when applied. *)
  hdr <- gethdr;
    match hdr_full hdr with
    | left _ => Ret TxnD.WriteErr
    | right pf =>
      (* here we've established that the log has at least one position left *)
      desc <- getdesc;
        _ <- writehdr (hdr_inc hdr pf);
        (* a crash here doesn't matter because [committed = false] and therefore
        the entire log is logically empty *)
        _ <- set_desc desc hdr.(log_length) a v;
          (* now the partial transaction has one more write; the descriptor
          block has the correct address at the new index, and the corresponding
          value is in the log at the paired address *)
      Ret TxnD.WriteOK
    end.

(** log_apply (which is also the recovery procedure) *)

(* Crashes during log_apply will leave the physical disk in a partial state,
where some of the committed writes have been applied, but log_apply always
starts at the beginning. Its sub-procedures [apply_at] and [apply_upto] only run
when [committed := true] and always have i < hdr.(log_length). *)

(* apply_at guarantees that index i in the log is applied *)
Definition apply_at desc (i:nat) :=
  a_v <- get_logwrite desc i;
    let '(a, v) := a_v in
    _ <- data_write a v;
      Ret tt.

(* [apply_upto] applies entries i through (len-1) from the log; if it crashes, the
log is still partially applied (and it doesn't much matter how much, since
log_apply always applies from the beginning).

 [apply_upto] maintains an invariant in its recursive subcalls that [i <=
 len]. *)
Fixpoint apply_upto desc i len :=
  match len with
  | 0 => Ret tt
  | S len =>
    _ <- apply_at desc i;
      apply_upto desc (i+1) len
  end.

(* log_apply is just a wrapper around apply_upto that reads the metadata; note
that it establishes the invariants of [apply_upto] by checking for a commit.

Its postcondition/recovery postcondition says the log is now empty, because it
explicitly sets the header. Note that the descriptor block does not need to be
changed because it's ignored with a log length of 0. *)
Definition log_apply :=
  hdr <- gethdr;
    _ <- if hdr.(committed) then
          desc <- getdesc;
            apply_upto desc 0 hdr.(log_length)
        else Ret tt;
    writehdr empty_hdr.

Definition commit :=
  hdr <- gethdr;
    _ <- writehdr (hdr_setcommit hdr);
    (* here we can crash in a committed state, where we need to apply *)
    log_apply.

Definition recovery := log_apply.
