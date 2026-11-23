/-
The proof of `internal.strconv.ParseInt`.
-/
module

public import Perennial.Spec.internal.strconv.ParseInt
public import Perennial.Spec.internal.strconv.ParseUint
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.ParseInt.wp_proof
    (wp_ParseUint : internal.strconv.ParseUint.spec (GF := GF) (hG := hG)) :
    internal.strconv.ParseInt.spec (GF := GF) (hG := hG) := by
  intro s base bitSize Hb1 Hb2 Hs1 Hs2
  wp_start
  wp_auto
  wp_if_destruct
  · iapply HΦ
    ipureintro
    simp only [internal.strconv.parseInt]
    constructor <;> first | trivial | rfl
  obtain ⟨c, cs, rfl⟩ : ∃ c cs, s = c :: cs := by
    cases s with
    | nil => exact absurd rfl Hif
    | cons c cs => exact ⟨c, cs, rfl⟩
  -- the sign
  wp_join iprop(∃ (t : GoString) (neg : Bool), "s" ∷ s_ptr ↦ t ∗ "neg" ∷ neg_ptr ↦ neg ∗
      "%Ht" ∷ ⌜internal.strconv.parseInt (c :: cs) (sint.nat base) (sint.nat bitSize) =
        internal.strconv.parseIntOf neg t (sint.nat base) (sint.nat bitSize)⌝) at next with [s neg]
    as ⟨%t, %neg, s, neg, %Ht⟩
  · wp_auto
    wp_if_destruct
    · -- `+`
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl
      rw [ite_eq_left (by simp only [List.length_cons] at Hl ⊢; word)]
      rw [show sint.nat (W64 ((W8 43 :: cs).length : Int)) = cs.length + 1 by
          simp only [List.length_cons] at Hl ⊢; word,
        List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
      wp_auto
      wp_join_done
      iexists cs, false
      iframe
      ipureintro
      simp [internal.strconv.parseInt]
    · have h43 := Hif
      wp_if_destruct
      · -- `-`
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hl
        rw [ite_eq_left (by simp only [List.length_cons] at Hl ⊢; word)]
        rw [show sint.nat (W64 ((W8 45 :: cs).length : Int)) = cs.length + 1 by
            simp only [List.length_cons] at Hl ⊢; word,
          List.drop_succ_cons, List.drop_zero, Nat.add_sub_cancel, List.take_length]
        wp_auto
        wp_join_done
        iexists cs, true
        iframe
        ipureintro
        simp [internal.strconv.parseInt]
      · -- no sign
        wp_join_done
        iexists (c :: cs), false
        iframe
        ipureintro
        simp only [internal.strconv.parseInt, if_neg Hif, if_neg h43]
  wp_apply wp_ParseUint t base bitSize Hb1 Hb2 Hs1 Hs2 as %x %err %Hout
  rcases hres : internal.strconv.parseUint t (sint.nat base) (sint.nat bitSize) with n | _ | _
  · -- a number
    rw [hres] at Hout
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    have hpo := hres
    have hnle := internal.strconv.parseUint_ok_le _ _ _ _ hres
    generalize hun : n = un at *
    have hun64 : un < 2 ^ 64 := by
      have : 2 ^ internal.strconv.effBitSize (sint.nat bitSize) ≤ 2 ^ 64 :=
        Nat.pow_le_pow_right (by decide) (by unfold internal.strconv.effBitSize; split <;> word)
      have : 1 ≤ 2 ^ internal.strconv.effBitSize (sint.nat bitSize) := Nat.one_le_two_pow
      omega
    wp_join iprop(∃ bs : w64, "bitSize" ∷ bitSize_ptr ↦ bs ∗
        "%Hbs" ∷ ⌜sint.nat bs = internal.strconv.effBitSize (sint.nat bitSize) ∧
          1 ≤ sint.Z bs ∧ sint.Z bs ≤ 64⌝) with [bitSize] as ⟨%bs, bitSize, %Hbs⟩
    · iexists _; iframe; ipureintro
      simp only [internal.strconv.effBitSize, show sint.nat (W64 0) = 0 from rfl, if_pos]
      refine ⟨?_, by word, by word⟩
      word
    · iexists _; iframe; ipureintro
      refine ⟨?_, ?_, by word⟩
      · simp only [internal.strconv.effBitSize, ite_eq_right (show ¬ sint.nat bitSize = 0 by
          intro h; apply Hif; word)]
      · have : bitSize ≠ W64 0 := Hif
        word
    have hE := Hbs.1
    have hbs1 : (bs - W64 1).toNat = internal.strconv.effBitSize (sint.nat bitSize) - 1 := by
      rw [← hE]; word
    have hEle : internal.strconv.effBitSize (sint.nat bitSize) ≤ 64 := by rw [← hE]; word
    have hC : (W64 1 <<< (bs - W64 1)).toNat =
        2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) := by
      rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, hbs1]
      have h1 : (W64 1).toNat = 1 := rfl
      rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have hC1 : 1 ≤ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) := Nat.one_le_two_pow
    have hC63 : 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) ≤ 2 ^ 63 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpo' : internal.strconv.parseIntOf neg t (sint.nat base) (sint.nat bitSize) =
        (if !neg ∧ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) ≤ un then
          .errRange (((2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) : Nat) : Int) - 1)
        else if neg ∧ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) < un then
          .errRange (-((2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) : Nat) : Int))
        else .ok (if neg then -(un : Int) else un)) := by
      unfold internal.strconv.parseIntOf; rw [hpo]
    generalize W64 1 <<< (bs - W64 1) = cv at *
    generalize 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) = C at *
    have hu : uint.Z (W64 (un : Int)) = un := by word
    have hcz : uint.Z cv = C := by word
    cases neg
    · -- no `-`
      rw [show (!false) = true from rfl]
      wp_auto
      wp_if_destruct
      · -- beyond the maximum
        iapply HΦ
        ipureintro
        rw [Ht, hpo', if_pos ⟨rfl, by omega⟩]
        exact ⟨by word, rfl⟩
      · iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp; omega), if_neg (by simp), if_neg (by simp)]
        exact ⟨by word, rfl⟩
    · -- `-`
      rw [show (!true) = false from rfl]
      wp_auto
      wp_if_destruct
      · -- below the minimum
        iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp), if_pos ⟨rfl, by omega⟩]
        exact ⟨by word, rfl⟩
      · iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp), if_neg (by simp; omega), if_pos rfl]
        exact ⟨by word, rfl⟩
  · -- a syntax error
    rw [hres] at Hout
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    iapply HΦ
    ipureintro
    rw [Ht]
    unfold internal.strconv.parseIntOf
    rw [hres]
    exact ⟨rfl, rfl⟩
  · -- a range error: the maximum, read as the value
    rw [hres] at Hout
    obtain ⟨rfl, rfl⟩ := Hout
    wp_auto
    have hpo := hres
    have hnle : 2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 ≤
        2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 := Nat.le_refl _
    generalize hun : 2 ^ internal.strconv.effBitSize (sint.nat bitSize) - 1 = un at hnle ⊢
    have hun64 : un < 2 ^ 64 := by
      have : 2 ^ internal.strconv.effBitSize (sint.nat bitSize) ≤ 2 ^ 64 :=
        Nat.pow_le_pow_right (by decide) (by unfold internal.strconv.effBitSize; split <;> word)
      have : 1 ≤ 2 ^ internal.strconv.effBitSize (sint.nat bitSize) := Nat.one_le_two_pow
      omega
    wp_join iprop(∃ bs : w64, "bitSize" ∷ bitSize_ptr ↦ bs ∗
        "%Hbs" ∷ ⌜sint.nat bs = internal.strconv.effBitSize (sint.nat bitSize) ∧
          1 ≤ sint.Z bs ∧ sint.Z bs ≤ 64⌝) with [bitSize] as ⟨%bs, bitSize, %Hbs⟩
    · iexists _; iframe; ipureintro
      simp only [internal.strconv.effBitSize, show sint.nat (W64 0) = 0 from rfl, if_pos]
      refine ⟨?_, by word, by word⟩
      word
    · iexists _; iframe; ipureintro
      refine ⟨?_, ?_, by word⟩
      · simp only [internal.strconv.effBitSize, ite_eq_right (show ¬ sint.nat bitSize = 0 by
          intro h; apply Hif; word)]
      · have : bitSize ≠ W64 0 := Hif
        word
    have hE := Hbs.1
    have hbs1 : (bs - W64 1).toNat = internal.strconv.effBitSize (sint.nat bitSize) - 1 := by
      rw [← hE]; word
    have hEle : internal.strconv.effBitSize (sint.nat bitSize) ≤ 64 := by rw [← hE]; word
    have hC : (W64 1 <<< (bs - W64 1)).toNat =
        2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) := by
      rw [BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, hbs1]
      have h1 : (W64 1).toNat = 1 := rfl
      rw [h1, Nat.shiftLeft_eq, Nat.one_mul]
      exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by omega))
    have hC1 : 1 ≤ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) := Nat.one_le_two_pow
    have hC63 : 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) ≤ 2 ^ 63 :=
      Nat.pow_le_pow_right (by decide) (by omega)
    have hpo' : internal.strconv.parseIntOf neg t (sint.nat base) (sint.nat bitSize) =
        (if !neg ∧ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) ≤ un then
          .errRange (((2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) : Nat) : Int) - 1)
        else if neg ∧ 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) < un then
          .errRange (-((2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) : Nat) : Int))
        else .ok (if neg then -(un : Int) else un)) := by
      unfold internal.strconv.parseIntOf; rw [hpo, ← hun]
    generalize W64 1 <<< (bs - W64 1) = cv at *
    generalize 2 ^ (internal.strconv.effBitSize (sint.nat bitSize) - 1) = C at *
    have hu : uint.Z (W64 (un : Int)) = un := by word
    have hcz : uint.Z cv = C := by word
    cases neg
    · -- no `-`
      rw [show (!false) = true from rfl]
      wp_auto
      wp_if_destruct
      · -- beyond the maximum
        iapply HΦ
        ipureintro
        rw [Ht, hpo', if_pos ⟨rfl, by omega⟩]
        exact ⟨by word, rfl⟩
      · iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp; omega), if_neg (by simp), if_neg (by simp)]
        exact ⟨by word, rfl⟩
    · -- `-`
      rw [show (!true) = false from rfl]
      wp_auto
      wp_if_destruct
      · -- below the minimum
        iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp), if_pos ⟨rfl, by omega⟩]
        exact ⟨by word, rfl⟩
      · iapply HΦ
        ipureintro
        rw [Ht, hpo', if_neg (by simp), if_neg (by simp; omega), if_pos rfl]
        exact ⟨by word, rfl⟩