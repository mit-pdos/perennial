/-
The proof of `time.fmtInt`.
-/
module

public import Perennial.Spec.time.fmtInt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.lt_pow10_pos {x : Int} {k : Nat} (h : x < 10 ^ k) (h1 : 1 ≤ x) : 1 ≤ k := by
  rcases k with _ | k
  · simp at h; omega
  · omega

theorem time.div10_lt_pow10 {x : Int} {k : Nat} (h : x < 10 ^ (k + 1)) :
    x / 10 < 10 ^ k := by
  rw [Int.pow_succ] at h
  exact Int.ediv_lt_of_lt_mul (by decide) h

theorem time.fmtInt.wp_proof : time.fmtInt.spec (GF := GF) (hG := hG) := by
  intro a xs v k hk1 hkl hv
  wp_start as Ha
  ihave %Hal := ownSlice_len _ _ _ $$ Ha
  obtain ⟨Hal, Hal0⟩ := Hal
  wp_auto
  wp_if_destruct
  · -- `v = 0`: one `0`
    have hl1 : 0 ≤ sint.Z (a.len - W64 1) ∧ sint.Z (a.len - W64 1) < sint.Z a.len := by
      constructor <;> word
    rw [if_pos hl1]
    obtain ⟨v0, hv0⟩ : ∃ v, xs[(sint.Z (a.len - W64 1)).toNat]? = some v :=
      ⟨_, List.getElem?_eq_getElem (by word)⟩
    icases ownSlice_elem_acc (V := w8) (sint.Z (a.len - W64 1)) v0 a _ _ hl1.1 hv0 $$ Ha with ⟨H0, Ha⟩
    wp_auto
    ihave Ha := Ha $$ H0
    iapply HΦ
    isplitr
    · ipureintro; constructor <;> word
    iexists _
    iframe Ha
    ipureintro; simp
  · -- the digits, from the last
    ihave IH : iprop(∃ (w vc : w64) (ys : List w8), "w" ∷ w_ptr ↦ w ∗ "v" ∷ v_ptr ↦ vc ∗
        "Ha" ∷ a ↦* ys ∗
        "%Hi" ∷ ⌜ys.length = xs.length ∧ xs.length - k ≤ sint.Z w ∧ sint.Z w ≤ xs.length ∧
          uint.Z vc < 10 ^ (k + sint.nat w - xs.length)⌝) $$ [w v Ha]
    · iexists a.len, v, xs
      iframe
      ipureintro
      refine ⟨rfl, by word, by word, ?_⟩
      rw [show k + sint.nat a.len - xs.length = k by omega]; exact hv
    wp_for IH
    wp_if_destruct
    · -- `vc > 0`: a digit at `w - 1`
      obtain ⟨hys, hw0, hwl, hvc⟩ := Hi
      have hvpos : 1 ≤ uint.Z vc := by
        have h0 : uint.Z (W64 0) = 0 := rfl
        omega
      have hk := time.lt_pow10_pos hvc hvpos
      have hw1 : xs.length - k + 1 ≤ sint.Z w := by
        have : 1 ≤ k + sint.nat w - xs.length := hk
        have : (sint.nat w : Int) = sint.Z w := by word
        omega
      have hl1 : 0 ≤ sint.Z (w - W64 1) ∧ sint.Z (w - W64 1) < sint.Z a.len := by
        constructor <;> word
      rw [if_pos hl1]
      obtain ⟨v0, hv0⟩ : ∃ v, ys[(sint.Z (w - W64 1)).toNat]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by word)⟩
      icases ownSlice_elem_acc (V := w8) (sint.Z (w - W64 1)) v0 a _ _ hl1.1 hv0 $$ Ha with ⟨H0, Ha⟩
      wp_auto
      ihave Ha := Ha $$ H0
      wp_for_post
      iframe
      iexists (w - W64 1), (vc / W64 10), _
      iframe
      ipureintro
      refine ⟨by simp [hys], by word, by word, ?_⟩
      have e : k + sint.nat w - xs.length = (k + sint.nat (w - W64 1) - xs.length) + 1 := by
        have : (sint.nat w : Int) = sint.Z w := by word
        have : sint.nat (w - W64 1) + 1 = sint.nat w := by word
        omega
      rw [e] at hvc
      have := time.div10_lt_pow10 hvc
      rw [show uint.Z (vc / W64 10) = uint.Z vc / 10 by word]
      exact this
    · -- done
      obtain ⟨hys, hw0, hwl, hvc⟩ := Hi
      iapply HΦ
      isplitr
      · ipureintro; exact ⟨hw0, hwl⟩
      iexists ys
      iframe Ha
      ipureintro; exact hys

end proof

end Perennial
