(* TODO: this isn't correct, the new translation needs certain go_type definitions *)
From Perennial.goose_lang.ffi Require Export disk_ffi.impl.
From New.golang Require Import defn.

#[global]
Existing Instances disk_op disk_model.
Section disk.

  Definition Disk : go_type := ptrT.

  Definition BlockSize :=
    #(W64 4096).

  Definition Getⁱᵐᵖˡ : val :=
    λ: <>, ExtV ().

  Definition Readⁱᵐᵖˡ : val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp (Var "a") in
    (InjL (Var "p", #(W64 4096), #(W64 4096))).

  Definition ReadToⁱᵐᵖˡ : val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp (Var "a") in
    slice.copy byteT (Var "buf") (Var "p", #(W64 4096), #(W64 4096)).

  Definition Writeⁱᵐᵖˡ : val :=
    λ: "a" "b",
    ExternalOp WriteOp (Var "a", slice.ptr (Var "b")).

  Definition Barrierⁱᵐᵖˡ : val :=
    λ: <>, #().

  Definition Sizeⁱᵐᵖˡ : val :=
    λ: "v",
       ExternalOp SizeOp (Var "v").

End disk.
