/-
The proof of `time.Timer.Stop`.
-/
module

public import Perennial.Spec.time.Timer__Stop
public import Perennial.Spec.time.stopTimer

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

theorem time.Timer.Stop.wp_proof
    (wp_stopTimer : time.stopTimer.spec (GF := GF) (hG := hG)) :
    time.Timer.Stop.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as Ht
  unfold isTimer isFuncTimer
  icases Ht with (⟨%ch, %γ, #HC, #Hinit, ⟨%fire, #Hcell, #Hfire⟩, #Hch⟩ | ⟨#Hinit, #Hrt⟩)
  · wp_auto
    wp_apply wp_stopTimer $$ [] as %b -
    · unfold isRuntimeTimer
      iexists fire
      iexact Hcell
    wp_end
  · wp_auto
    wp_apply wp_stopTimer $$ Hrt as %b -
    wp_end

end proof

end Perennial
