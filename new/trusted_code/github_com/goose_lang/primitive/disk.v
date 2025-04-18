(* TODO: this isn't correct, the new translation needs certain go_type definitions *)
From Perennial.goose_lang.ffi Require Export disk_ffi.impl.
From New.golang Require Import defn.

#[global]
Existing Instances disk_op disk_model.
Section disk.

  Definition Disk : go_type := ptrT.

  Definition BlockSize := BlockSize.

  Definition Get: val :=
    λ: <>, ExtV ().

  Definition Read: val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    (Var "p", #(W64 4096), #(W64 4096)).

  Definition ReadTo: val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp (Var "a") in
    slice.copy #byteT (Var "buf") (Var "p", #(W64 4096), #(W64 4096)).

  Definition Write: val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  Definition Barrier: val :=
    λ: <>, #().

  Definition Size: val :=
    λ: "v",
       ExternalOp SizeOp (Var "v").

End disk.
