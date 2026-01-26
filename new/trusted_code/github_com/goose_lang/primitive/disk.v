(* TODO: this isn't correct, the new translation needs certain go_type definitions *)
From Perennial.goose_lang.ffi Require Export disk_ffi.impl.
From New.golang Require Import defn.

(* This is generalized over {ext} so functions that are generalized over {ext}
   can refers to it. The only definition in a goose translation that is
   specialized to a concrete FFI is the Assumptions propclass.  So, only [ⁱᵐᵖˡ]
   stuff should be specializd to the ffi in trusted code. *)
Section disk_consts.
Context {ext : ffi_syntax} {go_gctx : GoGlobalContext}.
  Definition BlockSize : val :=
    #(W64 4096).
End disk_consts.

#[global]
Existing Instances disk_op disk_model.
Section disk.
Context {go_gctx : GoGlobalContext}.

  Definition Getⁱᵐᵖˡ : val :=
    λ: <>, ExtV ().

  Definition Readⁱᵐᵖˡ : val :=
    λ: "a",
    let: "p" := ExternalOp ReadOp "a" in
    FullSlice (go.ArrayType 4096 go.byte) ("p", #(W64 0), #(W64 4096), #(W64 4096)).

  Definition ReadToⁱᵐᵖˡ : val :=
    λ: "a" "buf",
    let: "p" := ExternalOp ReadOp "a" in
    FuncResolve "copy" [go.SliceType go.byte] #() "buf" ("p", #(W64 4096), #(W64 4096)).

  Definition Writeⁱᵐᵖˡ : val :=
    λ: "a" "b",
    ExternalOp WriteOp ("a", IndexRef (go.SliceType go.byte) ("b", #(W64 0))).

  Definition Barrierⁱᵐᵖˡ : val :=
    λ: <>, #().

  Definition Sizeⁱᵐᵖˡ : val :=
    λ: "v",
       ExternalOp SizeOp "v".

End disk.
