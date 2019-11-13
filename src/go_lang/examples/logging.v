From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lang struct slice typing.
From Perennial.go_lang Require Export ffi.disk.
From Perennial.go_lang Require Import proofmode notation.

Existing Instances disk_op disk_model disk_ty disk_semantics disk_interp.

Local Coercion Var' (s: string) : expr := Var s.

(** * Append-only, sequential, crash-safe log.

    The main interesting feature is that the log supports multi-block atomic
    appends, which are implemented by atomically updating an on-disk header with
    the number of valid blocks in the log.
 *)

Module log.
  Definition logS := mkStruct ["log_sz"; "disk_sz"].
  Definition T: ty := intT * intT.
  Section fields.
    Context `{ext_ty:ext_types}.
    Definition log_sz := structF! logS "log_sz".
    Definition disk_sz := structF! logS "disk_sz".
    Theorem log_sz_t Γ : Γ ⊢ log_sz : (T -> intT).
    Proof.
      typecheck.
    Qed.
    Theorem disk_sz_t Γ : Γ ⊢ disk_sz : (T -> intT).
    Proof.
      typecheck.
    Qed.
  End fields.
End log.

Hint Resolve log.log_sz_t log.disk_sz_t : types.

Import log.

Definition write_hdr: val :=
  λ: "log",
    let: "hdr" := NewByteSlice #4096 in
    UInt64Put (log_sz "log") "hdr";;
    UInt64Put (disk_sz "log") (SliceSkip "hdr" #8);;
    Write #0 "hdr".

Theorem write_hdr_t Γ : Γ ⊢ write_hdr : (T -> unitT).
Proof.
  typecheck.
Qed.

Definition init: val :=
  λ: "disk_sz",
  if: "disk_sz" < #1 then (zero_val log.T, #false)
  else
    let: "log" := (#0, "disk_sz") in
    write_hdr "log";;
    ("log", #true).

Theorem init_t Γ : Γ ⊢ init : (intT -> T * boolT).
Proof.
  typecheck.
Qed.

Definition get: val :=
  λ: "log" "i",
  let: "sz" := log.log_sz "log" in
  if: "i" < "sz"
  then (Read (#1+"i"), #true)
  else (slice.nil, #false).

Theorem get_t Γ : Γ ⊢ get : (T -> intT -> slice.T byteT * boolT).
Proof.
  typecheck.
Qed.

Definition write_all: val :=
  λ: "bks" "off",
  let: "len" := slice.len "bks" in
  for: "i" < "len" :=
    let: "bk" := SliceGet "bks" "i" in
    Write ("off" + "i") "bk".

Theorem write_all_t Γ : Γ ⊢ write_all : (slice.T (slice.T byteT) -> intT -> unitT).
Proof.
  typecheck.
Qed.

Hint Resolve write_all_t : types.

Definition append: val :=
  λ: "logp" "bks",
  let: "log" := !"logp" in
  let: "sz" := log.log_sz "log" in
  if: #1 + "sz" + slice.len "bks" ≥ log.disk_sz "log" then
    #false
  else
    write_all "bks" (#1 + "sz");;
    let: "new_log" := ("sz" + slice.len "bks", log.disk_sz "log") in
    write_hdr "new_log";;
    "logp" <- "new_log";;
    #true.

Theorem append_t Γ : Γ ⊢ append : (refT T -> slice.T (slice.T byteT) -> boolT).
Proof.
  typecheck.
Qed.

Definition reset: val :=
  λ: "logp",
  let: "new_log" := (#0, log.disk_sz !"logp") in
  write_hdr "new_log";;
  "logp" <- "new_log";;
  #().

Theorem reset_t Γ : Γ ⊢ reset : (refT T -> unitT).
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

Theorem recover_t Γ : Γ ⊢ recover : (unitT -> T).
Proof.
  typecheck.
Qed.
