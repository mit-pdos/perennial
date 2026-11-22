/-
The proof of `countPairs` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs

/-- `0 + 1 + ... + (m - 1)`. -/
def tri : Nat → Nat
  | 0 => 0
  | j + 1 => tri j + j

theorem tri_int (m : Nat) : (tri m : Int) = (m : Int) * ((m : Int) - 1) / 2 := by
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [tri]
    have h : ((k + 1 : Nat) : Int) * (((k + 1 : Nat) : Int) - 1) = (k : Int) * ((k : Int) - 1) + 2 * k := by
      push_cast; grind
    rw [h, Int.add_mul_ediv_left _ _ (by decide)]
    push_cast; omega

theorem tri_mono (a b : Nat) (h : a ≤ b) : tri a ≤ tri b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ k ih =>
    rcases Nat.lt_or_ge a (k + 1) with h' | h'
    · have := ih (by omega); simp only [tri]; omega
    · have : a = k + 1 := by omega
      subst this; exact Nat.le_refl _

theorem tri_bound (m : Nat) (h : m < 2 ^ 32) : tri m < 2 ^ 63 := by
  have h1 := tri_int m
  have h2 : (m : Int) * ((m : Int) - 1) < 2 ^ 64 := by
    have : (m : Int) * ((m : Int) - 1) ≤ (m : Int) * (m : Int) := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have : (m : Int) * (m : Int) < 2 ^ 32 * 2 ^ 32 := by
      have hm : (m : Int) < 2 ^ 32 := by exact_mod_cast h
      have := Int.mul_le_mul_of_nonneg_left (show (m:Int) ≤ 2^32 - 1 by omega) (show (0:Int) ≤ m by omega)
      have := Int.mul_le_mul_of_nonneg_right (show (m:Int) ≤ 2^32 - 1 by omega) (show (0:Int) ≤ 2^32 - 1 by omega)
      omega
    omega
  omega

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs

section proof
open github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs.spec (GF := GF) (hG := hG) := by
  intro n hn
  wp_start
  wp_auto
  have hnb : uint.nat n < 2 ^ 32 := by word
  ihave HI : (∃ i c : w64,
      "i" ∷ i_ptr ↦ i ∗
      "c" ∷ c_ptr ↦ c ∗
      "%Hi" ∷ ⌜uint.nat i ≤ uint.nat n ∧ uint.nat c = tri (uint.nat i)⌝ : IProp GF) $$ [i c]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by word, by simp [tri]; rfl⟩
  wp_for HI
  wp_if_destruct
  · have hb := tri_bound (uint.nat n) hnb
    have hm := tri_mono (uint.nat i + 1) (uint.nat n) (by word)
    ihave HJ : (∃ j c' : w64,
        "j" ∷ j_ptr ↦ j ∗
        "c" ∷ c_ptr ↦ c' ∗
        "%Hj" ∷ ⌜uint.nat j ≤ uint.nat i ∧ uint.nat c' = tri (uint.nat i) + uint.nat j⌝ : IProp GF)
      $$ [j c]
    · iexists _, _
      iframe
      ipureintro; exact ⟨by word, by rw [Hi.2]; word⟩
    wp_for HJ
    wp_if_destruct
    · -- `continue L` ends the iteration of the outer loop
      have hj : j = i := by word
      subst hj
      wp_for_post
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      constructor
      · word
      · rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word]
        simp only [tri]; exact Hj.2
    · have hji : uint.nat j < uint.nat i := by
        have : uint.nat j ≠ uint.nat i := fun h => Hif (by word)
        omega
      have : tri (uint.nat i + 1) = tri (uint.nat i) + uint.nat i := rfl
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      constructor
      · word
      · rw [show uint.nat (j + W64 1) = uint.nat j + 1 by word,
          show uint.nat (c' + W64 1) = uint.nat c' + 1 by word]
        omega
  · have hi : uint.nat i = uint.nat n := by word
    have hc := tri_int (uint.nat n)
    rw [hi] at Hi
    rw [show c = W64 (uint.Z n * (uint.Z n - 1) / 2) by
      have : (uint.nat n : Int) = uint.Z n := by word
      rw [this] at hc
      rw [← hc, ← Hi.2]; word]
    iapply HΦ
    iexact Hpre

end proof

end Perennial
