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
    Context {ext:ext_op}.
    Definition log_sz := structF! logS "log_sz".
    Definition disk_sz := structF! logS "disk_sz".
  End fields.
End log.

Import log.

Definition write_hdr: val :=
  λ: "log",
    let: "hdr" := NewByteSlice #4096 in
    UInt64Put "log_sz" "hdr";;
    UInt64Put "disk_sz" ("hdr" +ₗ #8);;
    Write #0 "hdr".

Definition init: val :=
  λ: "disk_sz",
  if: "disk_sz" < #1 then (zero_val log.T, #false)
  else
    let: "log" := (#0, "disk_sz") in
    write_hdr "log";;
    ("log", #true).

Definition get: val :=
  λ: "log" "i",
  let: "sz" := log.log_sz "log" in
  if: "i" < "sz"
  then (Read (#1+"i"), #true)
  else (slice.nil, #false).

Definition write_all: val :=
  λ: "bks" "off",
  let: "len" := slice.len "bks" in
  for: "i" < "len" :=
    let: "bk" := SliceGet "bks" "i" in
    Write ("off" + "i") "bk".

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

Definition reset: val :=
  λ: "logp",
  let: "new_log" := (#0, log.disk_sz !"log") in
  write_hdr "new_log";;
  "logp" <- "new_log";;
  #().

Definition recover: val :=
  λ: <>,
     let: "hdr" := Read #0 in
     let: "log_sz" := UInt64Get ("hdr", #8) in
     let: "disk_sz" := UInt64Get (("hdr" +ₗ #8), #8) in
     let: "log" := ("log_sz", "disk_sz") in
     "log".
