/-
The proof of `time.Ticker.Reset`.
-/
module

public import Perennial.Spec.time.Ticker__Reset
public import Perennial.Spec.time.when
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

theorem time.Ticker.Reset.wp_proof
    (wp_when : time.when.spec (GF := GF) (hG := hG))
    (wp_resetTimerAt : time.resetTimerAt.spec (GF := GF) (hG := hG)) :
    time.Ticker.Reset.spec (GF := GF) (hG := hG) := by
  intro t d
  wp_start as ⟨%Hd, %ch, %γ, #Ht⟩
  unfold isTicker
  icases Ht with ⟨#HC, #Hinit, ⟨%fire, #Hcell, #Hfire⟩, #Hch⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  try wp_auto
  wp_apply wp_when as %w %Hw
  wp_apply wp_resetTimerAt $$ [] as %b -
  · isplitr
    · ipureintro; constructor <;> word
    iexists fire
    iframe #
  wp_end

end proof

end Perennial
