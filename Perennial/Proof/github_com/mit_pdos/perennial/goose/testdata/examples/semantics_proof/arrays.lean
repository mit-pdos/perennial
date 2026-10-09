/-
Proofs of the array tests of the goose `semantics` test package (range loops
over arrays).
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

/-- `for i, x := range [3]uint64{1, 2, 3}` adds `x + i` to `sum`; `j` counts
the iterations (the loop's own counter). -/
theorem wp_testRangeArrayLit : TestFunOk (GF := GF) testRangeArrayLit := by
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

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
