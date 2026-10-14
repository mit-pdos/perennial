/-
The proof of `context.(*cancelCtx).Value`.
-/
module

public import Perennial.Spec.context.cancelCtx__Value

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.cancelCtx.Value.wp_proof :
    context.cancelCtx.Value.spec (GF := GF) (hG := hG) := fun c γ P => by
  wp_start as #Hc
  unfold cancelCtxKeyAny
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
