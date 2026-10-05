/-
Port of `new/golang/theory/assume.v`: specs for `assume` and the overflow
assumptions built on it.
-/
import Perennial.Golang.Theory.PostLifting
import Perennial.Golang.Defn.Assume
import Perennial.Std.Word.Automation
import Perennial.Std.Word.MulOverflow

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]
variable {s : Stuckness} {E : CoPset}

theorem wp_assume (b : Bool) (Φ : val → IProp GF) :
    iprop(⌜b = true⌝ -∗ Φ #()) ⊢ WP (App (Val assume) (Val #b)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  cases b
  · wp_pures
    iclear HΦ
    iloeb as IH
    wp_pure
    iexact IH
  · wp_pures
    iapply HΦ
    ipureintro; rfl

theorem wp_assumeSumNoOverflow (x y : w64) (Φ : val → IProp GF) :
    iprop(⌜uint.Z x + uint.Z y < 2 ^ 64⌝ -∗ Φ #()) ⊢
      WP (App (App (Val assumeSumNoOverflow) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_apply_core wp_assume
  iintro %H
  wp_pures
  iapply HΦ
  ipureintro
  simp only [decide_eq_true_eq] at H
  word

theorem wp_sumAssumeNoOverflow (x y : w64) (Φ : val → IProp GF) :
    iprop(⌜uint.Z x + uint.Z y < 2 ^ 64⌝ -∗ Φ #(x + y)) ⊢
      WP (App (App (Val sumAssumeNoOverflow) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_apply_core wp_assumeSumNoOverflow
  iintro %H
  wp_pures
  iapply HΦ
  ipureintro; exact H

theorem wp_assumeSumNoOverflowSigned (x y : w64) (Φ : val → IProp GF) :
    iprop(⌜-2 ^ 63 ≤ sint.Z x + sint.Z y ∧ sint.Z x + sint.Z y < 2 ^ 63⌝ -∗ Φ #()) ⊢
      WP (App (App (Val assumeSumNoOverflowSigned) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  by_cases h1 : sint.Z (W64 0) < sint.Z y
  · simp only [decide_eq_true h1, ↓reduceIte]
    wp_pures
    by_cases h2 : sint.Z x < sint.Z (W64 (2 ^ 63 - 1) - y)
    · simp only [decide_eq_true h2, ↓reduceIte]
      wp_pures
      wp_apply_core wp_assume
      iintro %_
      iapply HΦ
      ipureintro
      constructor <;> word
    · simp only [decide_eq_false h2, Bool.false_eq_true, ↓reduceIte]
      wp_pures
      have h3 : ¬ sint.Z y < sint.Z (W64 0) := by word
      simp only [decide_eq_false h3, Bool.false_eq_true, ↓reduceIte]
      wp_pures
      wp_apply_core wp_assume
      iintro %H
      exact absurd H (by decide)
  · simp only [decide_eq_false h1, Bool.false_eq_true, ↓reduceIte]
    wp_pures
    by_cases h3 : sint.Z y < sint.Z (W64 0)
    · simp only [decide_eq_true h3, ↓reduceIte]
      wp_pures
      by_cases h4 : sint.Z (W64 (-2 ^ 63) - y) < sint.Z x
      · simp only [decide_eq_true h4, ↓reduceIte]
        wp_pures
        wp_apply_core wp_assume
        iintro %_
        iapply HΦ
        ipureintro
        constructor <;> word
      · simp only [decide_eq_false h4, Bool.false_eq_true, ↓reduceIte]
        wp_pures
        wp_apply_core wp_assume
        iintro %H
        exact absurd H (by decide)
    · simp only [decide_eq_false h3, Bool.false_eq_true, ↓reduceIte]
      wp_pures
      wp_apply_core wp_assume
      iintro %H
      exact absurd H (by decide)

theorem wp_sumAssumeNoOverflowSigned (x y : w64) (Φ : val → IProp GF) :
    iprop(⌜-2 ^ 63 ≤ sint.Z x + sint.Z y ∧ sint.Z x + sint.Z y < 2 ^ 63⌝ -∗ Φ #(x + y)) ⊢
      WP (App (App (Val sumAssumeNoOverflowSigned) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_apply_core wp_assumeSumNoOverflowSigned
  iintro %H
  wp_pures
  iapply HΦ
  ipureintro; exact H

theorem wp_mulOverflows (x y : w64) (Φ : val → IProp GF) :
    Φ #(decide (2 ^ 64 ≤ uint.Z x * uint.Z y)) ⊢
      WP (App (App (Val mulOverflows) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  by_cases hx : x = W64 0
  · subst hx
    wp_pures
    have h0 : uint.Z (W64 0) = 0 := by word
    have : ¬ (2 ^ 64 ≤ uint.Z (W64 0) * uint.Z y) := by rw [h0]; omega
    simp only [decide_eq_false this]
    iexact HΦ
  · simp only [decide_eq_false hx, Bool.false_eq_true, ↓reduceIte]
    wp_pures
    by_cases hy : y = W64 0
    · subst hy
      wp_pures
      have h0 : uint.Z (W64 0) = 0 := by word
      have : ¬ (2 ^ 64 ≤ uint.Z x * uint.Z (W64 0)) := by rw [h0]; omega
      simp only [decide_eq_false this]
      iexact HΦ
    · simp only [decide_eq_false hy, Bool.false_eq_true, ↓reduceIte]
      wp_pures
      have hx' : uint.Z x ≠ 0 := by intro h; apply hx; word
      have hy' : uint.Z y ≠ 0 := by intro h; apply hy; word
      have hc := mul_overflow_check_correct x y hx' hy'
      have hmax : uint.Z (W64 (2 ^ 64 - 1)) = 2 ^ 64 - 1 := by rfl
      have hdiv : uint.Z (W64 (2 ^ 64 - 1) / y) = (2 ^ 64 - 1) / uint.Z y := by
        rw [← hmax]; simp only [uint.Z, BitVec.toNat_udiv]; push_cast; rfl
      have key : uint.Z (W64 (2 ^ 64 - 1) / y) < uint.Z x ↔ 2 ^ 64 ≤ uint.Z x * uint.Z y := by
        rw [hdiv, ← hc]; omega
      simp only [key]
      iexact HΦ

theorem wp_assumeMulNoOverflow (x y : w64) (Φ : val → IProp GF) :
    iprop(⌜uint.Z x * uint.Z y < 2 ^ 64⌝ -∗ Φ #()) ⊢
      WP (App (App (Val assumeMulNoOverflow) (Val #x)) (Val #y)) @ s; E {{ Φ }} := by
  iintro HΦ
  wp_call
  wp_apply_core wp_mulOverflows
  wp_pures
  wp_apply_core wp_assume
  iintro %H
  iapply HΦ
  ipureintro
  by_cases h : 2 ^ 64 ≤ uint.Z x * uint.Z y
  · simp only [decide_eq_true h, Bool.not_true] at H
    exact absurd H (by decide)
  · omega

end wps

end Perennial
