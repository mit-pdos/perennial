/-
The proof of `time.Ticker.Stop`.
-/
module

public import Perennial.Spec.time.Ticker__Stop
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

theorem time.Ticker.Stop.wp_proof
    (wp_stopTimerAt : time.stopTimerAt.spec (GF := GF) (hG := hG)) :
    time.Ticker.Stop.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as ⟨%ch, %γ, #Ht⟩
  unfold isTicker
  icases Ht with ⟨#HC, #Hinit, ⟨%fire, #Hcell, #Hfire⟩, #Hch⟩
  wp_auto
  wp_apply wp_stopTimerAt $$ [] as %b -
  · unfold isRuntimeTimer
    iexists fire
    iexact Hcell
  wp_end

end proof

end Perennial
