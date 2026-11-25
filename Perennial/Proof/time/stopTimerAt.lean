/-
The proof of `time.stopTimerAt`.
-/
module

public import Perennial.Spec.time.stopTimerAt
public import Perennial.Spec.time.runtimeTimerFire
public import Perennial.Spec.internal.gomodel.Choose

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

theorem time.stopTimerAt.wp_proof
    (wp_runtimeTimerFire : time.runtimeTimerFire.spec (GF := GF) (hG := hG))
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG)) :
    time.stopTimerAt.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as #Ht
  unfold isRuntimeTimer
  icases Ht with ⟨%fire, #Hcell⟩
  wp_auto
  wp_apply wp_runtimeTimerFire $$ Hcell
  wp_apply wp_Choose as %b -
  wp_end

end proof

end Perennial
