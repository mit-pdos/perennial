/-
The proof of `time.makeTimerChan`.
-/
module

public import Perennial.Spec.time.makeTimerChan
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

theorem time.makeTimerChan.wp_proof
    (wp_Choose : internal.gomodel.Choose.spec (GF := GF) (hG := hG)) :
    time.makeTimerChan.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_Choose as %b -
  wp_if_destruct
  all_goals first
    | (wp_apply chan.wp_make1 (V := time.Time) as %ch %γ ⟨#His, -, Hown⟩
       iapply HΦ
       iintro %Ψ
       iapply start_bag Ψ _ ch γ trivial $$ His Hown)
    | (wp_apply chan.wp_make2 (V := time.Time) $$ [] as %ch %γ ⟨#His, -, Hown⟩
       · ipureintro; decide
       iapply HΦ
       iintro %Ψ
       iapply start_bag Ψ _ ch γ (by simp) $$ His Hown)

end proof

end Perennial
