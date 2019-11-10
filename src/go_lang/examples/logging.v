From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From Perennial.go_lang Require Export lang struct slice.
From Perennial.go_lang Require Export ffi.disk.
From Perennial.go_lang Require Import proofmode notation.

Existing Instances disk_op disk_model disk_semantics disk_interp.

Local Coercion Var' (s: string) : expr := Var s.

(** * Append-only, seqeuntial, crash-safe log.

    The main interesting feature is that the log supports multi-block atomic
    appends, which are implemented by atomically updating an on-disk header with
    the number of valid blocks in the log.
 *)

Module log.
  Definition logS := mkStruct ["log_sz"; "disk_sz"].
  Section fields.
    Context {ext:ext_op}.
    Definition log_sz := structF! logS "log_sz".
    Definition disk_sz := structF! logS "disk_sz".
  End fields.
End log.

Import log.

Definition write_hdr: val :=
  λ: "log",
    let: "hdr" := AllocN #4096 #(LitByte 0) in
    EncodeInt "log_sz" "hdr";;
    EncodeInt "disk_sz" ("hdr" +ₗ #8);;
    ExternalOp Write (#0, "hdr").

Definition init: val :=
  λ: "disk_sz",
  if: "disk_sz" < #1 then NONE
  else
    let: "log" := (#0, "disk_sz") in
    write_hdr "log";;
    SOME "log".

Definition get: val :=
  λ: "log" "i",
  let: "sz" := log.log_sz "log" in
  if: "i" < "sz"
  then SOME (ExternalOp Read (#1+"i"))
  else NONE.

Definition write_all: val :=
  λ: "bks" "off",
  let: "len" := slice.len "bks" in
  for: "i" < "len" :=
    let: "bk" := SliceGet "bks" "i" in
    ExternalOp Write ("off" + "i", "bk").

Definition append: val :=
  λ: "log" "bks",
  if: #1 + log.log_sz "log" + slice.len "bks" ≥ log.disk_sz "log" then
    NONEV
  else
    write_all "bks" (#1 + log.log_sz "log");;
    let: "new_log" := (log.log_sz "log" + slice.len "bks", log.disk_sz "log") in
    write_hdr "new_log";;
    SOME "new_log".

Definition reset: val :=
  λ: "log",
  let: "new_log" := (#0, log.disk_sz "log") in
  write_hdr "new_log";;
  "new_log".

Definition recover: val :=
  λ: <>,
     let: "hdr" := ExternalOp Read #0 in
     let: "log_sz" := DecodeInt "hdr" in
     let: "disk_sz" := DecodeInt ("hdr" +ₗ #8) in
     let: "log" := ("log_sz", "disk_sz") in
     "log".
