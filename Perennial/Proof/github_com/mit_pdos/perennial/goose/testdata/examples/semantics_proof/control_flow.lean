/-
Proofs of the control-flow tests of the goose `semantics` test package
(`fallthrough`, and `break` in a `switch`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testFallthrough : TestFunOk (GF := GF) testFallthrough := by
  semantics_auto

theorem wp_testFallthroughReturn : TestFunOk (GF := GF) testFallthroughReturn := by
  semantics_auto

theorem wp_testEmptyBlock : TestFunOk (GF := GF) testEmptyBlock := by
  semantics_auto

/-- Each `break` ends the `switch`, so every iteration increments `n`. -/
theorem wp_testBreakSwitch : TestFunOk (GF := GF) testBreakSwitch := by
  semantics_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "HΦ" ∷ Φ #true ∗
      "%Hi" ∷ ⌜n = i ∧ uint.Z i ≤ 3⌝ : IProp GF) $$ [i n HΦ]
  · iexists _, _
    iframe
    ipureintro; exact ⟨rfl, by decide⟩
  wp_for HI
  wp_if_destruct
  · repeat (first | wp_if_destruct | wp_auto)
    · wp_for_post
      iexists _, _
      iframe
      ipureintro; word
    · by_cases h2 : i = W64 2
      · subst h2
        wp_auto
        wp_for_post
        iexists _, _
        iframe
        ipureintro; word
      · simp only [h2, decide_false]
        wp_auto
        wp_for_post
        iexists _, _
        iframe
        ipureintro; word
  · iapply exact_eq ?_ $$ HΦ
    have : n = W64 3 := by word
    simp [this]

/-- Case 0 falls through into case 1, whose `break` ends the `switch`. -/
theorem wp_testFallthroughBreak : TestFunOk (GF := GF) testFallthroughBreak := by
  semantics_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "HΦ" ∷ Φ #true ∗
      "%Hi" ∷ ⌜(i = W64 0 ∧ n = W64 0) ∨ (i = W64 1 ∧ n = W64 101) ∨
        (i = W64 2 ∧ n = W64 211)⌝ : IProp GF) $$ [i n HΦ]
  · iexists _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  · wp_for_post
    iexists _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, rfl⟩
  · wp_for_post
    iexists _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, rfl⟩
  · iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
