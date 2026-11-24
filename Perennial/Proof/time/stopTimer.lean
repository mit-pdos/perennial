/-
The proof of `time.stopTimer`.
-/
module

public import Perennial.Spec.time.stopTimer
public import Perennial.Spec.time.stopTimerAt

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

theorem time.stopTimer.wp_proof
    (wp_stopTimerAt : time.stopTimerAt.spec (GF := GF) (hG := hG)) :
    time.stopTimer.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as #Ht
  wp_auto
  wp_apply wp_stopTimerAt $$ Ht as %b -
  wp_end

end proof

end Perennial
