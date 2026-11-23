/-
The proof of `bytes.Buffer.WriteByte`.
-/
module

public import Perennial.Spec.bytes.Buffer__WriteByte
public import Perennial.Spec.bytes.Buffer__grow
public import Perennial.Spec.bytes.Buffer__tryGrowByReslice

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : bytes.Assumptions]

theorem bytes.Buffer.WriteByte.wp_proof
    (wp_tryGrowByReslice : bytes.Buffer.tryGrowByReslice.spec (GF := GF) (hG := hG))
    (wp_grow : bytes.Buffer.grow.spec (GF := GF) (hG := hG)) :
    bytes.Buffer.WriteByte.spec (GF := GF) (hG := hG) := by
  intro l bs c
  wp_start as Hown
  unfold bytes.ownBuffer
  icases Hown with ⟨%b, %all, Hl, Hbuf, Hcap, %Hoff⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hoff ⊢
  iStructNamed Hl
  wp_auto
  simp only [bytes.opInvalid]
  wp_auto
  ihave Hl : l ↦ (⟨bb, off, W8 0⟩ : bytes.Buffer) $$ [buf off lastRead]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  rw [Hoff.2.2]
  wp_apply wp_tryGrowByReslice l ⟨bb, off, W8 0⟩ all (W64 1) $$ [$Hl $Hbuf $Hcap] as %i %ok Hres
  · ipureintro; exact ⟨by decide, Hoff.1, Hoff.2.1⟩
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨-, Hl, Hbuf, Hcap⟩
    try wp_auto
    wp_apply wp_grow l ⟨bb, off, W8 0⟩ all (W64 1) $$ [$Hl $Hbuf $Hcap] as %i Hg
    · ipureintro; exact ⟨by decide, by unfold maxAddr; decide, Hoff.1, Hoff.2.1⟩
    iunfold bytes.bufferGrown at Hg
    icases Hg with ⟨%b2, %all2, Hl, Hbuf, Hcap, %Hg⟩
    ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Hl
    ihave %Hlen2 := ownSlice_len $$ Hbuf
    obtain ⟨bb2, off2, lr2⟩ := b2
    simp only at Hg Hlen2 ⊢
    iStructNamed Hl
    try wp_auto
    have Hi : 0 ≤ sint.Z i ∧ sint.Z i < all2.length := by
      have := Hg.2.2.1; constructor <;> word
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z bb2.len := by
      have := Hlen2.1; constructor <;> word
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index bb2 (sint.Z i) all2 c $$ [Hbuf] as Hbuf
    · iframe; ipureintro; exact Hi
    try wp_auto
    iapply HΦ
    iexists ⟨bb2, off2, lr2⟩, all2.set (sint.nat i) c
    iframe Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn2
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    have hlen : all2.length = sint.nat i + 1 := by have := Hg.2.2.1; word
    have hset : all2.set (sint.nat i) c = all2.take (sint.nat i) ++ [c] := by
      apply List.ext_getElem
      · simp [hlen]
      · intro k h1 h2
        simp only [List.length_set] at h1
        rw [List.getElem_set]
        by_cases hk : k = sint.nat i
        · subst hk
          rw [List.getElem_append_right (by simp; omega)]
          simp [hlen]
        · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hk), List.getElem_append_left (by simp; omega)]
          simp
    refine ⟨Hg.1, by rw [List.length_set]; word, ?_⟩
    rw [hset, List.drop_append_of_le_length (by simp; word), Hg.2.2.2]
  · simp only [↓reduceIte]
    irename Hres => Hg
    iunfold bytes.bufferGrown at Hg
    icases Hg with ⟨%b2, %all2, Hl, Hbuf, Hcap, %Hg⟩
    ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Hl
    ihave %Hlen2 := ownSlice_len $$ Hbuf
    obtain ⟨bb2, off2, lr2⟩ := b2
    simp only at Hg Hlen2 ⊢
    iStructNamed Hl
    try wp_auto
    have Hi : 0 ≤ sint.Z i ∧ sint.Z i < all2.length := by
      have := Hg.2.2.1; constructor <;> word
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z bb2.len := by
      have := Hlen2.1; constructor <;> word
    simp only [Hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index bb2 (sint.Z i) all2 c $$ [Hbuf] as Hbuf
    · iframe; ipureintro; exact Hi
    try wp_auto
    iapply HΦ
    iexists ⟨bb2, off2, lr2⟩, all2.set (sint.nat i) c
    iframe Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn2
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    have hlen : all2.length = sint.nat i + 1 := by have := Hg.2.2.1; word
    have hset : all2.set (sint.nat i) c = all2.take (sint.nat i) ++ [c] := by
      apply List.ext_getElem
      · simp [hlen]
      · intro k h1 h2
        simp only [List.length_set] at h1
        rw [List.getElem_set]
        by_cases hk : k = sint.nat i
        · subst hk
          rw [List.getElem_append_right (by simp; omega)]
          simp [hlen]
        · rw [ite_eq_right_iff.mpr (fun h => absurd h.symm hk), List.getElem_append_left (by simp; omega)]
          simp
    refine ⟨Hg.1, by rw [List.length_set]; word, ?_⟩
    rw [hset, List.drop_append_of_le_length (by simp; word), Hg.2.2.2]

end proof

end Perennial
