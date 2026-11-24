/-
The proof of `strings.makeASCIISet`.
-/
module

public import Perennial.Spec.strings.makeASCIISet
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace strings

private theorem bit_shift (x : w8) :
    W32 1 <<< W64 (uint.Z (x % W8 32)) = BitVec.twoPow 32 (x % W8 32).toNat := by
  rw [BitVec.shiftLeft_eq']
  have : (W64 (uint.Z (x % W8 32))).toNat = (x % W8 32).toNat := by
    simp [W64]; omega
  rw [this]; rfl

private theorem twoPow_ne (k : Nat) (hk : k < 32) : BitVec.twoPow 32 k ≠ 0#32 := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_twoPow, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hk)] at this
  have := Nat.two_pow_pos k; rw [BitVec.toNat_zero] at *; omega

/-- Setting bit `c % 32` of a word: bit `c' % 32` is then set iff it was or `c % 32 = c' % 32`. -/
private theorem bit_or (w : w32) (c c' : w8) :
    (!decide ((w ||| W32 1 <<< W64 (uint.Z (c % W8 32))) &&& W32 1 <<< W64 (uint.Z (c' % W8 32)) =
      W32 0)) =
    Bool.or (!decide (w &&& W32 1 <<< W64 (uint.Z (c' % W8 32)) = W32 0))
      (decide (c % W8 32 = c' % W8 32)) := by
  have hk : (c % W8 32).toNat < 32 := by simp [W8]; omega
  have hk' : (c' % W8 32).toNat < 32 := by simp [W8]; omega
  rw [bit_shift, bit_shift, BitVec.and_twoPow, BitVec.and_twoPow]
  have h0 : W32 0 = 0#32 := rfl
  rw [h0]
  have hne := twoPow_ne _ hk'
  have heq : (c % W8 32 = c' % W8 32) ↔ (c % W8 32).toNat = (c' % W8 32).toNat :=
    BitVec.toNat_inj.symm
  by_cases hx : w.getLsbD (c' % W8 32).toNat <;> by_cases he : c % W8 32 = c' % W8 32 <;>
    (simp_all; try exact fun h => absurd h.symm he)

/-- `as[c/32] |= 1 << (c%32)` adds `c` to the set. -/
private theorem asciiSetHas_set (vs : List w32) (c c' : w8) (w : w32)
    (hw : vs[c.toNat / 32]? = some w) :
    asciiSetHas ⟨vs.set (c.toNat / 32) (w ||| W32 1 <<< W64 (uint.Z (c % W8 32)))⟩ c' =
      Bool.or (asciiSetHas ⟨vs⟩ c') (decide (c' = c)) := by
  unfold asciiSetHas
  simp only [List.getD_eq_getElem?_getD]
  by_cases hq : c'.toNat / 32 = c.toNat / 32
  · rw [hq, List.getElem?_set_self (by
      rcases Nat.lt_or_ge (c.toNat / 32) vs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hw), hw]
    simp only [Option.getD_some]
    rw [bit_or]
    congr 1
    have : (c % W8 32 = c' % W8 32) ↔ c' = c := by
      constructor
      · intro h; apply BitVec.eq_of_toNat_eq
        have := congrArg BitVec.toNat h; simp [W8] at this; omega
      · rintro rfl; rfl
    exact decide_eq_decide.2 this
  · rw [List.getElem?_set_ne (Ne.symm hq)]
    have : c' ≠ c := fun h => hq (by rw [h])
    simp [this]

private theorem asciiSetHas_zero (c : w8) :
    asciiSetHas ⟨List.replicate 8 (W32 0)⟩ c = false := by
  unfold asciiSetHas
  have : c.toNat / 32 < 8 := by have := c.isLt; omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate, this,
    ↓reduceIte, Option.getD_some]
  simp

end strings

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.makeASCIISet.wp_proof :
    strings.makeASCIISet.spec (GF := GF) (hG := hG) := by
  intro chars
  wp_start as %Hascii
  wp_auto
  irename «as» => Has
  have hz : (zero_val (GoArray w32 8)) = ⟨List.replicate 8 (W32 0)⟩ := rfl
  rw [hz]
  ihave HI : (∃ (j : Nat) (vs : List w32), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "Has" ∷ as_ptr ↦ (⟨vs⟩ : GoArray w32 8) ∗
      "%Hj" ∷ ⌜j ≤ chars.length ∧ vs.length = 8 ∧
        ∀ c, strings.asciiSetHas ⟨vs⟩ c = decide (c ∈ chars.take j)⌝ : IProp GF) $$ [i Has]
  · iexists 0, _
    iframe
    ipureintro
    refine ⟨Nat.zero_le _, rfl, fun c => ?_⟩
    rw [strings.asciiSetHas_zero]; simp
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j < chars.length := by have := Hj.1; revert Hif; word
    have Hk : sint.nat (W64 (j : Int)) = j := by word
    have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    obtain ⟨c, Hc⟩ : ∃ c, chars[j]? = some c := ⟨_, List.getElem?_eq_getElem Hjl⟩
    have Hc128 : uint.Z c < 128 := Hascii c (List.mem_of_getElem? Hc)
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hc]
    try wp_auto
    wp_if_destruct
    · exfalso; revert Hif; word
    try wp_auto
    have hi : sint.Z (W64 (uint.Z (c / W8 32))) = ((c.toNat / 32 : Nat) : Int) := by word
    have hlt : c.toNat / 32 < vs.length := by have := c.isLt; omega
    rw [ite_eq_left (by word)]
    icases array_acc (V := w32) as_ptr (sint.Z (W64 (uint.Z (c / W8 32)))) _ 8 ⟨vs⟩
      vs[c.toNat / 32] (by word)
      (by rw [hi, Int.toNat_natCast]; exact List.getElem?_eq_getElem hlt) $$ Has with ⟨Hel, Hclose⟩
    try wp_auto
    rw [ite_eq_left (by word)]
    try wp_auto
    ihave Has := Hclose $$ Hel
    rw [hi, Int.toNat_natCast]
    wp_for_post
    iframe
    iexists j + 1, _
    isplitl [i]
    · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
      iexact i
    iframe
    ipureintro
    refine ⟨by omega, by simp [Hj.2.1], fun c' => ?_⟩
    rw [strings.asciiSetHas_set vs c c' _ (List.getElem?_eq_getElem hlt), Hj.2.2 c',
      List.take_add_one, Hc, Option.toList_some]
    simp
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j = chars.length := by have := Hj.1; revert Hif; word
    simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    ipureintro
    refine ⟨Hj.2.1, fun c => ?_⟩
    rw [Hj.2.2 c, Hjl, List.take_length]

end proof

end Perennial
