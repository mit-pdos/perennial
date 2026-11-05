/-
The proof of `time.Timer.Reset` (translated; the runtime's `resetTimer` is modeled in `TrustedCode/time.lean`).
-/
module

public import Perennial.Spec.time.Timer__Reset
public import Perennial.Spec.time.when

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

theorem time.Timer.Reset.wp_proof
    (wp_when : time.when.spec (GF := GF) (hG := hG)) :
    time.Timer.Reset.spec (GF := GF) (hG := hG) := by
  intro t ch γ d
  wp_start as Ht
  unfold isTimer
  icases Ht with ⟨#HC, #Hinit, #Hrt, #Hch⟩
  wp_auto
  wp_apply wp_when as %w -
  wp_func_call
  wp_apply wp_resetTimer as %b -
  all_goals try iexact Hrt
  wp_end

end proof

end Perennial
