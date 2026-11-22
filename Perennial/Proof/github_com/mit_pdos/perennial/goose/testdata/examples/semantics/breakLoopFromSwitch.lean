/-
The proof of `breakLoopFromSwitch` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.breakLoopFromSwitch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.breakLoopFromSwitch.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.breakLoopFromSwitch.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "%Hi" ∷ ⌜(i = W64 0 ∧ n = W64 0) ∨ (i = W64 1 ∧ n = W64 1) ∨ (i = W64 2 ∧ n = W64 1) ∨
        (i = W64 3 ∧ n = W64 2)⌝ : IProp GF) $$ [i n]
  · iexists _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  all_goals repeat (first | wp_if_destruct | wp_auto)
  all_goals wp_for_post
  · -- `i = 0`: the default case
    iframe; iexists _, _; iframe
    ipureintro; right; left; constructor <;> word
  · -- `i = 1`: the unlabeled `break` ends only the `switch`
    iframe; iexists _, _; iframe
    ipureintro; right; right; left; constructor <;> word
  · iframe; iexists _, _; iframe
    ipureintro; right; right; right; constructor <;> word
  · -- `i = 3`: `break L` ends the loop
    iapply HΦ
    iexact Hpre

end proof

end Perennial
