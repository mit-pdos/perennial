/-
The proof of `returnInLabeledLoop` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.returnInLabeledLoop

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.returnInLabeledLoop.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.returnInLabeledLoop.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i : w64,
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜i = W64 0 ∨ i = W64 1 ∨ i = W64 2⌝ : IProp GF) $$ [i]
  · iexists _
    iframe
    ipureintro; left; rfl
  wp_for HI
  wp_if_destruct
  · ihave HJ : (∃ j : w64,
        "j" ∷ j_ptr ↦ j ∗
        "%Hj" ∷ ⌜uint.Z j ≤ uint.Z i + 2 ∧ (i = W64 2 → uint.Z j ≤ 3)⌝ : IProp GF) $$ [j]
    · iexists _
      iframe
      ipureintro; constructor <;> word
    wp_for HJ
    wp_if_destruct
    · rcases Hi with rfl | rfl | rfl
      all_goals repeat (first | wp_if_destruct | wp_auto)
      · exfalso; word
      · by_cases hc : uint.Z (W64 0 + W64 1) < uint.Z j
        · -- `continue L`
          rw [decide_eq_true hc]
          wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; right; left; word
        · rw [decide_eq_false hc]
          wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; constructor <;> word
      · exfalso; word
      · by_cases hc : uint.Z (W64 1 + W64 1) < uint.Z j
        · -- `continue L`
          rw [decide_eq_true hc]
          wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; right; right; word
        · rw [decide_eq_false hc]
          wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; constructor <;> word
      · -- `return` from the inner loop at `i = 2`, `j = 3`
        have hj : j = W64 3 := by word
        subst hj
        wp_for_post
        wp_for_post
        rw [show W64 2 * W64 10 + W64 3 = W64 23 by word]
        iapply HΦ
        iexact Hpre
      · by_cases hc : uint.Z (W64 2 + W64 1) < uint.Z j
        · -- `continue L`
          rw [decide_eq_true hc]
          wp_auto
          wp_for_post
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; exfalso; word
        · rw [decide_eq_false hc]
          wp_auto
          wp_for_post
          iframe
          iexists _
          iframe
          ipureintro; constructor <;> word
    · -- the inner loop never ends normally
      exfalso; rcases Hi with rfl | rfl | rfl <;> word
  · exfalso; rcases Hi with rfl | rfl | rfl <;> word

end proof

end Perennial
