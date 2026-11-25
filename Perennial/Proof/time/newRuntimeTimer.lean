/-
The proof of `time.newRuntimeTimer`.
-/
module

public import Perennial.Spec.time.newRuntimeTimer

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

/-- Over the primitive stub `newRuntimeTimer.impl` (`TrustedCode/time.lean`). -/
theorem time.newRuntimeTimer.wp_proof : time.newRuntimeTimer.spec (GF := GF) (hG := hG) := by
  intro fire
  wp_start
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  iStructNamed t
  ipersist initTimer
  wp_apply wp_runtimeTimerAlloc as #Hrt
  iapply HΦ
  iframe #
  iexists _
  iexact C

end proof

end Perennial
