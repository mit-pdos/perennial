From Perennial.go_lang Require Import prelude.
From Perennial.go_lang Require Import ffi.disk.
Existing Instances disk_op disk_model disk_ty.

Local Coercion Var' (s: string) : expr := Var s.

(** * Append-only, sequential, crash-safe log.

    The main interesting feature is that the log supports multi-block atomic
    appends, which are implemented by atomically updating an on-disk header with
    the number of valid blocks in the log.
 *)

Module log.
  Definition S := mkStruct ["sz"; "disk_sz"].
  Definition T: ty := intT * intT.
  Section fields.
    Context `{ext_ty:ext_types}.
    Definition sz := structF! S "sz".
    Definition disk_sz := structF! S "disk_sz".
    Theorem sz_t : ⊢ sz : (T -> intT).
    Proof.
      typecheck.
    Qed.
    Theorem disk_sz_t : ⊢ disk_sz : (T -> intT).
    Proof.
      typecheck.
    Qed.
  End fields.
End log.

Hint Resolve log.sz_t log.disk_sz_t : types.

Definition write_hdr: val :=
  λ: "log",
    let: "hdr" := NewSlice byteT #4096 in
    UInt64Put (log.sz "log") "hdr";;
    UInt64Put (log.disk_sz "log") (SliceSkip "hdr" #8);;
    Write #0 "hdr".

Theorem write_hdr_t : ⊢ write_hdr : (log.T -> unitT).
Proof.
  typecheck.
Qed.

Definition init: val :=
  λ: "disk_sz",
  if: "disk_sz" < #1 then (zero_val log.T, #false)
  else
    let: "log" := buildStruct log.S ["sz" ::= #0; "disk_sz" ::= "disk_sz"] in
    write_hdr "log";;
    ("log", #true).

Theorem init_t : ⊢ init : (intT -> log.T * boolT).
Proof.
  typecheck.
Qed.

Definition get: val :=
  λ: "log" "i",
  let: "sz" := log.sz "log" in
  if: "i" < "sz"
  then (Read (#1+"i"), #true)
  else (slice.nil, #false).

Theorem get_t : ⊢ get : (log.T -> intT -> slice.T byteT * boolT).
Proof.
  typecheck.
Qed.

Definition write_all: val :=
  λ: "bks" "off",
  let: "len" := slice.len "bks" in
  for: "i" < "len" :=
    let: "bk" := SliceGet "bks" "i" in
    Write ("off" + "i") "bk".

Theorem write_all_t : ⊢ write_all : (slice.T (slice.T byteT) -> intT -> unitT).
Proof.
  typecheck.
Qed.

Hint Resolve write_all_t : types.

Definition append: val :=
  λ: "logp" "bks",
  let: "log" := !"logp" in
  let: "sz" := log.sz "log" in
  if: #1 + "sz" + slice.len "bks" ≥ log.disk_sz "log" then
    #false
  else
    write_all "bks" (#1 + "sz");;
    let: "new_log" := ("sz" + slice.len "bks", log.disk_sz "log") in
    write_hdr "new_log";;
    "logp" <- "new_log";;
    #true.

Theorem append_t : ⊢ append : (refT log.T -> slice.T (slice.T byteT) -> boolT).
Proof.
  typecheck.
Qed.

Definition reset: val :=
  λ: "logp",
  let: "new_log" := (#0, log.disk_sz !"logp") in
  write_hdr "new_log";;
  "logp" <- "new_log";;
  #().

Theorem reset_t : ⊢ reset : (refT log.T -> unitT).
Proof.
  typecheck.
Qed.

Definition recover: val :=
  λ: <>,
     let: "hdr" := Read #0 in
     let: "log_sz" := UInt64Get (SliceTake "hdr" #8) in
     let: "disk_sz" := UInt64Get (SliceTake (SliceSkip "hdr" #8) #8) in
     let: "log" := ("log_sz", "disk_sz") in
     "log".

Theorem recover_t : ⊢ recover : (unitT -> log.T).
Proof.
  typecheck.
Qed.
