/-
The proof of `encoding/binary.PutUvarint`.
-/
module

public import Perennial.Spec.encoding.binary.PutUvarint

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.binary.Assumptions]

open encoding.binary in
theorem encoding.binary.PutUvarint.wp_proof :
    encoding.binary.PutUvarint.spec (GF := GF) (hG := hG) := fun buf xs x hn => by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  wp_auto
  -- `buf` holds the bytes `P` written so far, and `P ++ uvarintEnc x' = uvarintEnc x`
  ihave HL : (∃ (P : List w8) (xv iv : w64),
      "x" ∷ x_ptr ↦ xv ∗ "i" ∷ i_ptr ↦ iv ∗
      "Hb" ∷ buf ↦* (P ++ xs.drop P.length) ∗
      "%Hinv" ∷ ⌜sint.Z iv = P.length ∧ P ++ uvarintEnc (uint.nat xv) = uvarintEnc (uint.nat x)⌝ :
        IProp GF) $$ [x i Hb]
  · iexists [], x, W64 0
    simp only [List.nil_append, List.length_nil, List.drop_zero]
    iframe
    ipureintro; simp
  wp_for HL
  obtain ⟨hiv, hP⟩ := Hinv
  have hn63 : (xs.length : Int) < 2 ^ 63 := by rw [Hlen.1]; word
  have hlenP : P.length + (uvarintEnc (uint.nat xv)).length ≤ xs.length := by
    have := congrArg List.length hP; simp at this; omega
  have hpos : 0 < (uvarintEnc (uint.nat xv)).length := by
    obtain ⟨V', c, he, -⟩ := uvarintEnc_spec (uint.nat xv); rw [he]; simp
  have hlenl : (P ++ xs.drop P.length).length = xs.length := by simp; omega
  wp_if_destruct
  · -- a continuation byte (`varint.go:54`)
    have h128 : 128 ≤ uint.nat xv := by
      have : uint.Z (W64 128) = 128 := rfl
      simp only [uint.nat, uint.Z] at Hif this ⊢; omega
    rw [ite_eq_left ⟨by omega, by rw [hiv]; have := Hlen.2; word⟩]
    wp_apply wp_store_slice_index $$ [Hb] as Hb
    · iframe; ipureintro; rw [hlenl]; omega
    wp_for_post
    iframe
    iexists P ++ [BitVec.ofNat 8 (xv.toNat % 128 + 128)], xv >>> W64 7, iv + W64 1
    rw [hiv, Int.toNat_natCast, byte_or_128]
    have hset : (P ++ List.drop P.length xs).set P.length (BitVec.ofNat 8 (xv.toNat % 128 + 128)) =
        P ++ [BitVec.ofNat 8 (xv.toNat % 128 + 128)] ++
          List.drop (P ++ [BitVec.ofNat 8 (xv.toNat % 128 + 128)]).length xs := by
      rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
      have : P.length < xs.length := by omega
      rw [List.drop_eq_getElem_cons this, List.set_cons_zero]
      simp
    rw [hset]
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      rw [this, hiv]; simp
    · rw [← hP, uvarintEnc_step xv h128]; simp
  · -- the last byte (`varint.go:58`)
    have h128 : uint.nat xv < 128 := by
      have : uint.Z (W64 128) = 128 := rfl
      simp only [uint.nat, uint.Z] at Hif this ⊢; omega
    rw [uvarintEnc_last xv h128] at hP
    rw [ite_eq_left ⟨by omega, by rw [hiv]; have := Hlen.2; word⟩]
    wp_apply wp_store_slice_index $$ [Hb] as Hb
    · iframe; ipureintro; rw [hlenl]; omega
    wp_auto
    have hW : iv + W64 1 = W64 ((uvarintEnc (uint.nat x)).length : Int) := by
      rw [← hP]
      simp only [List.length_append, List.length_singleton]
      apply BitVec.eq_of_toInt_eq
      have : sint.Z (iv + W64 1) = sint.Z iv + 1 := by word
      show sint.Z (iv + W64 1) = sint.Z (W64 ((P.length + 1 : Nat) : Int))
      rw [this, hiv]
      have : sint.Z (W64 ((P.length + 1 : Nat) : Int)) = ((P.length + 1 : Nat) : Int) := by
        simp only [sint.Z, W64, BitVec.toInt_ofInt]
        apply Int.bmod_eq_of_le <;> omega
      rw [this]; simp
    rw [hW]
    iapply HΦ
    rw [← hP, hiv, Int.toNat_natCast]
    have hset : (P ++ List.drop P.length xs).set P.length (W8 (uint.Z xv)) =
        P ++ [W8 (uint.Z xv)] ++ List.drop (P ++ [W8 (uint.Z xv)]).length xs := by
      rw [List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
      have : P.length < xs.length := by omega
      rw [List.drop_eq_getElem_cons this, List.set_cons_zero]
      simp
    rw [hset]
    iexact Hb

end proof

end Perennial
