/-
The proof of `testRangeArrayLit` (a goose semantics test, `arrays.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeArrayLit

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeArrayLit.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeArrayLit.spec (GF := GF) (hG := hG) := by
  semantics_auto
  rename_i k_ptr
  irename i => Hj
  irename : k_ptr ↦ (zero_val w64) => Hk
  ihave HI : (∃ j s xv kv : w64,
      "Hj" ∷ i_ptr ↦ j ∗
      "sum" ∷ sum_ptr ↦ s ∗
      "x" ∷ x_ptr ↦ xv ∗
      "Hk" ∷ k_ptr ↦ kv ∗
      "HΦ" ∷ Φ #true ∗
      "%Hj" ∷ ⌜(j = W64 0 ∧ s = W64 0) ∨ (j = W64 1 ∧ s = W64 1) ∨
        (j = W64 2 ∧ s = W64 4) ∨ (j = W64 3 ∧ s = W64 9)⌝ : IProp GF) $$ [Hj sum x Hk HΦ]
  · iexists _, _, _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  · wp_for_post
    iexists _, _, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by decide⟩
  · wp_for_post
    iexists _, _, _, _
    iframe
    ipureintro; right; right; left; exact ⟨rfl, by decide⟩
  · wp_for_post
    iexists _, _, _, _
    iframe
    ipureintro; right; right; right; exact ⟨rfl, by decide⟩
  · iexact HΦ

end proof

end Perennial
