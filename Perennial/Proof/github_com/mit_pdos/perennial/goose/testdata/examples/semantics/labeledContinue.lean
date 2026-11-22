/-
The proof of `labeledContinue` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue

/-- `0 + 1 + ... + (j - 1)`, the inner loop's sum after `j` iterations. -/
def tri : Nat → Nat
  | 0 => 0
  | j + 1 => tri j + j

/-- The sum after `i` outer iterations: iteration `i` adds `0 + ... + i`. -/
def total : Nat → Nat
  | 0 => 0
  | i + 1 => total i + tri (i + 1)

theorem tri_succ (j : Nat) : tri (j + 1) = tri j + j := rfl
theorem total_succ (i : Nat) : total (i + 1) = total i + tri (i + 1) := rfl

theorem tri_le (j : Nat) (h : j ≤ 4) : tri j ≤ 6 := by
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem total_le (i : Nat) (h : i ≤ 4) : total i ≤ 10 := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue

section proof
open github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledContinue.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i sum : w64,
      "i" ∷ i_ptr ↦ i ∗
      "sum" ∷ sum_ptr ↦ sum ∗
      "%Hi" ∷ ⌜uint.nat i ≤ 4 ∧ uint.nat sum = total (uint.nat i)⌝ : IProp GF) $$ [i sum]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by word, rfl⟩
  wp_for HI
  wp_if_destruct
  · have htot := total_le (uint.nat i) Hi.1
    ihave HJ : (∃ j sum' : w64,
        "j" ∷ j_ptr ↦ j ∗
        "sum" ∷ sum_ptr ↦ sum' ∗
        "%Hj" ∷ ⌜uint.nat j ≤ uint.nat i + 1 ∧ uint.nat j ≤ 4 ∧
          uint.nat sum' = total (uint.nat i) + tri (uint.nat j)⌝ : IProp GF) $$ [j sum]
    · iexists _, _
      iframe
      ipureintro; exact ⟨by word, by word, by rw [Hi.2]; rfl⟩
    wp_for HJ
    have htri := tri_le (uint.nat j) Hj.2.1
    wp_if_destruct
    · wp_if_destruct
      · -- `continue L`: the outer post statement runs
        have hj : uint.nat j = uint.nat i + 1 := by word
        wp_for_post
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        constructor
        · word
        · rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word, total_succ, ← hj]
          exact Hj.2.2
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        have := tri_succ (uint.nat j)
        refine ⟨by word, by word, ?_⟩
        rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word]
        word
    · -- the inner loop ends normally at `j = 4`, with `i = 3`
      have hj : uint.nat j = 4 := by word
      have hi : uint.nat i = 3 := by word
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      rw [hj, hi] at Hj
      have : total 4 = total 3 + tri 4 := rfl
      constructor
      · word
      · rw [show uint.nat (i + W64 1) = 4 by word]; omega
  · have hi : uint.nat i = 4 := by word
    rw [show sum = W64 10 by rw [hi] at Hi; have : total 4 = 10 := rfl; word]
    iapply HΦ
    iexact Hpre

end proof

end Perennial
