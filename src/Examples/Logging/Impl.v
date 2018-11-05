Require Import POCS.

Require Import Examples.Logging.TxnDiskAPI.
Require Import Examples.ReplicatedDisk.OneDiskAPI.

Require Import Helpers.Array.

Import ProcNotations.
Local Open Scope proc.

Module D := OneDisk.
Module TxnD := TxnDisk.

(* disk layout:

| log header (1 block) | descriptor block (1 block) |
| log region (LOG_LENGTH blocks; see below) | data region |
*)

(* The descriptor block encodes 32-bit addresses; it fits 1024byte/32bits = 256
addresses. *)
Definition LOG_LENGTH: nat := 256.
Definition __log_length_calculation: LOG_LENGTH = blockbytes / 4
  := eq_refl.

Record LogHdr :=
  { committed: bool;
    log_length: nat;
    log_length_ok: log_length <= LOG_LENGTH; }.

Record Descriptor :=
  { addresses: list addr;
    (* TODO: restrict addrs to be < 2^256 (-258) *)
    addresses_length:
      length addresses = 256; }.

Record block_encoder T :=
  { encode: T -> block;
    decode: block -> T;
    encode_decode: forall (x:T), decode (encode x) = x; }.

Axiom LogHdr_fmt: block_encoder LogHdr.
Axiom Descriptor_fmt: block_encoder Descriptor.

Definition read a := Prim (D.op_read a).
Definition write a v := Prim (D.op_write a v).
Definition size := Prim (D.op_size).

Definition log_read a :=
  read (2+LOG_LENGTH + a).

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

Definition hdr_setcommit (hdr:LogHdr) (should_commit:bool) : LogHdr :=
  {| committed := should_commit;
     log_length := hdr.(log_length);
     log_length_ok := hdr.(log_length_ok); |}.

Definition getdesc: proc D.Op Descriptor :=
  b <- read 1;
    Ret (Descriptor_fmt.(decode) b).

Definition writedesc (ds:Descriptor) :=
  write 1 (Descriptor_fmt.(encode) ds).

Definition add_addr (ds:Descriptor) (idx:nat) (a:addr) : Descriptor.
  refine {| addresses := assign ds.(addresses) idx a; |}.
  rewrite assign_length.
  apply ds.(addresses_length).
Defined.

Definition log_write a v :=
  hdr <- gethdr;
    match hdr_full hdr with
    | left _ => Ret TxnD.WriteErr
    | right pf =>
      desc <- getdesc;
        _ <- writehdr (hdr_inc hdr pf);
        let log_addr := hdr.(log_length) in
        _ <- writedesc (add_addr desc log_addr a);
        _ <- write (2+log_addr) v;
      Ret TxnD.WriteOK
    end.

Definition apply_at desc (i:nat) :=
  v <- read (1+i);
    let a := sel desc.(addresses) i in
    write a v.

Fixpoint apply_upto desc i len :=
  match len with
  | 0 => Ret tt
  | S len =>
    _ <- apply_at desc i;
      apply_upto desc (i+1) len
  end.

Definition log_apply :=
  hdr <- gethdr;
    _ <- if hdr.(committed) then
          desc <- getdesc;
            apply_upto desc 0 hdr.(log_length)
        else Ret tt;
    writehdr (hdr_setcommit hdr false).

Definition commit :=
  hdr <- gethdr;
    _ <- writehdr (hdr_setcommit hdr true);
    log_apply.
