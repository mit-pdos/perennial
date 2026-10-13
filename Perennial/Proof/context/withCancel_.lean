/-
The proof of `context.withCancel`.
-/
module

public import Perennial.Spec.context.withCancel_

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : context.Assumptions]

theorem context.withCancel.wp_proof :
    context.withCancel.spec (GF := GF) (hG := hG) := fun parent P Pre Hprop => by
  wp_start as ⟨#Hcci, Hpre⟩
  wp_auto
  icases «$r0_al» with %hal
  imod cancelCtx_alloc «$r0_ptr» P iprop(True) hal $$ Hcci «$r0» [] with ⟨%γ, #Hc, FContext⟩
  · itrivial
  ihave #Hc' := isCancelCtxOfR_of _ _ _ _ $$ Hc
  iapply wp_fupd
  wp_apply Hprop «$r0_ptr» γ $$ [$Hc' FContext Hpre] as HC
  · iframe
  dsimp only [ctxField]
  ipersist HC
  imodintro
  iapply HΦ
  iframe #

end proof

end Perennial
