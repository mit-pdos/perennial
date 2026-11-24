/-
The proof of `time.resetTimer`.
-/
module

public import Perennial.Spec.time.resetTimer
public import Perennial.Spec.time.resetTimerAt

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

theorem time.resetTimer.wp_proof
    (wp_resetTimerAt : time.resetTimerAt.spec (GF := GF) (hG := hG)) :
    time.resetTimer.spec (GF := GF) (hG := hG) := by
  intro t w p
  wp_start as Hpre
  wp_auto
  wp_apply wp_resetTimerAt $$ Hpre as %b -
  wp_end

end proof

end Perennial
