/-
The proof of `time.Timer.Stop` (translated; the runtime's `stopTimer` is modeled in `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.Timer__Stop

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

theorem time.Timer.Stop.wp_proof : time.Timer.Stop.spec (GF := GF) (hG := hG) := by
  intro t
  wp_start as Ht
  unfold isTimer isFuncTimer
  icases Ht with (⟨%ch, %γ, #HC, #Hinit, #Hrt, #Hch⟩ | ⟨#Hinit, #Hrt⟩)
  all_goals
    wp_auto
    wp_func_call
    wp_apply wp_stopTimer as %b -
    all_goals try iexact Hrt
    wp_end

end proof

end Perennial
