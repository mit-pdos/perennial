/-
The proof of `time.newRuntimeTicker`.
-/
module

public import Perennial.Spec.time.newRuntimeTicker

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Over the primitive stub `newRuntimeTicker.impl` (`TrustedCode/time.lean`). -/
theorem time.newRuntimeTicker.wp_proof : time.newRuntimeTicker.spec (GF := GF) (hG := hG) := by
  intro fire
  wp_start
  rw [show go.GoType.Named go!"time.Ticker" [] = time.Ticker.ty by with_unfolding_all rfl]
  wp_auto
  iStructNamed t
  ipersist initTicker
  wp_apply wp_runtimeTimerAlloc as #Hrt
  iapply HΦ
  iframe #
  iexists _
  iexact C

end proof

end Perennial
