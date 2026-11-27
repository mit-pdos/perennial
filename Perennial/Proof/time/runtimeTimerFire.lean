/-
The proof of `time.runtimeTimerFire`.
-/
module

public import Perennial.Spec.time.runtimeTimerFire

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

/-- Over the primitive stub `runtimeTimerFire.impl` (`TrustedCode/time.lean`). -/
theorem time.runtimeTimerFire.wp_proof : time.runtimeTimerFire.spec (GF := GF) (hG := hG) := by
  intro t fire
  wp_start as #Hcell
  unfold runtimeTimerCell runtimeTimerRef runtimeTimerType
  rw [show go.GoType.Named go!"time.Timer" [] = time.Timer.ty by with_unfolding_all rfl]
  wp_auto
  wp_end

end proof

end Perennial
