/-
The proof of `time.Timer.Reset`.
-/
module

public import Perennial.Spec.time.Timer__Reset
public import Perennial.Spec.time.when
public import Perennial.Spec.time.resetTimer

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
    (wp_when : time.when.spec (GF := GF) (hG := hG))
    (wp_resetTimer : time.resetTimer.spec (GF := GF) (hG := hG)) :
    time.Timer.Reset.spec (GF := GF) (hG := hG) := by
  intro t ch γ d
  wp_start as Ht
  unfold isTimer
  icases Ht with ⟨#HC, #Hinit, ⟨%fire, #Hcell, #Hfire⟩, #Hch⟩
  wp_auto
  wp_apply wp_when as %w %Hw
  wp_apply wp_resetTimer $$ [] as %b -
  · isplitr
    · ipureintro; constructor <;> word
    iexists fire
    iframe #
  wp_end

end proof

end Perennial
