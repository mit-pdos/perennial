/-
The proof of `bytes.Buffer.Write`.
-/
module

public import Perennial.Spec.bytes.Buffer__Write
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

theorem bytes.Buffer.Write.wp_proof
    (wp_tryGrowByReslice : bytes.Buffer.tryGrowByReslice.spec (GF := GF) (hG := hG))
    (wp_grow : bytes.Buffer.grow.spec (GF := GF) (hG := hG)) :
    bytes.Buffer.Write.spec (GF := GF) (hG := hG) := by
  intro l bs p dq d
  wp_start as ⟨Hown, Hp⟩
  unfold bytes.ownBuffer
  icases Hown with ⟨%b, %all, Hl, Hbuf, Hcap, %Hoff⟩
  ihave %Hlenp := ownSlice_len $$ Hp
  ihave %Hpb := ownSlice_bytes_len_le $$ Hp
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
  wp_apply wp_tryGrowByReslice l ⟨bb, off, W8 0⟩ all p.len $$ [$Hl $Hbuf $Hcap] as %i %ok Hres
  · ipureintro; exact ⟨Hlenp.2, Hoff.1, Hoff.2.1⟩
  cases ok
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hres with ⟨-, Hl, Hbuf, Hcap⟩
    try wp_auto
    wp_apply wp_grow l ⟨bb, off, W8 0⟩ all p.len $$ [$Hl $Hbuf $Hcap] as %i Hg
    · ipureintro; exact ⟨Hlenp.2, Hpb, Hoff.1, Hoff.2.1⟩
    iunfold bytes.bufferGrown at Hg
    icases Hg with ⟨%b2, %all2, Hl, Hbuf, Hcap, %Hg⟩
    ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Hl
    ihave %Hlen2 := ownSlice_len $$ Hbuf
    ihave %Hwf2 := ownSlice_wf $$ Hbuf
    obtain ⟨bb2, off2, lr2⟩ := b2
    simp only at Hg Hlen2 Hwf2 ⊢
    iStructNamed Hl
    try wp_auto
    have Hi2 : sint.Z bb2.len = sint.Z i + sint.Z p.len := by
      have := Hg.2.2.1; rw [this] at Hlen2; have := Hlen2.1; word
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z bb2.len ∧ sint.Z bb2.len ≤ sint.Z bb2.cap :=
      ⟨by omega, by omega, Hwf2.2⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases (ownSlice_split_all i bb2 _ _ ⟨by omega, by omega⟩).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
    try wp_auto
    wp_apply wp_slice_copy_int $$ [$Hbuf2 $Hp] as %k ⟨%Hk, Hbuf2, Hp⟩
    have Hdl : (all2.drop (sint.nat i)).length = d.length := by
      rw [List.length_drop, Hg.2.2.1, ← Hlenp.1]; omega
    have hz : List.drop d.length (List.drop (sint.nat i) all2) = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [hz, List.append_nil, Hdl, List.take_of_length_le (l := d) (Nat.le_refl _)]
    have hil : (all2.take (sint.nat i)).length = sint.nat i := by
      rw [List.length_take]; have := Hg.2.2.1; omega
    ihave Hbuf := ownSlice_combine (GF := GF) (V := w8) i bb2 (DFrac.own 1) _ d (W64 0) bb2.len
      ⟨by rw [hil, show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero], by decide, Hb.1, Hb.2.1⟩ $$ Hbuf1 Hbuf2
    ihave Hbuf := ownSlice_trivial_slice_2 $$ Hbuf
    have Hkd : k = W64 (d.length : Int) := by
      have hdb : (d.length : Int) ≤ 2 ^ 47 := by
        have := Hpb; unfold maxAddr at this; rw [Hlenp.1]; word
      apply BitVec.eq_of_toInt_eq; change sint.Z k = sint.Z (W64 _); rw [Hk]; word
    rw [Hkd]
    iapply HΦ
    iframe Hp
    iexists ⟨bb2, off2, lr2⟩, all2.take (sint.nat i) ++ d
    iframe Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn2
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    refine ⟨Hg.1, by simp only [List.length_append, hil]; word, ?_⟩
    rw [List.drop_append_of_le_length (by rw [hil]; word), Hg.2.2.2]
  · simp only [↓reduceIte]
    irename Hres => Hg
    iunfold bytes.bufferGrown at Hg
    icases Hg with ⟨%b2, %all2, Hl, Hbuf, Hcap, %Hg⟩
    ihave %Hnn2 := typedPointsto_not_null _ _ _ $$ Hl
    ihave %Hlen2 := ownSlice_len $$ Hbuf
    ihave %Hwf2 := ownSlice_wf $$ Hbuf
    obtain ⟨bb2, off2, lr2⟩ := b2
    simp only at Hg Hlen2 Hwf2 ⊢
    iStructNamed Hl
    try wp_auto
    have Hi2 : sint.Z bb2.len = sint.Z i + sint.Z p.len := by
      have := Hg.2.2.1; rw [this] at Hlen2; have := Hlen2.1; word
    have Hb : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z bb2.len ∧ sint.Z bb2.len ≤ sint.Z bb2.cap :=
      ⟨by omega, by omega, Hwf2.2⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases (ownSlice_split_all i bb2 _ _ ⟨by omega, by omega⟩).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
    try wp_auto
    wp_apply wp_slice_copy_int $$ [$Hbuf2 $Hp] as %k ⟨%Hk, Hbuf2, Hp⟩
    have Hdl : (all2.drop (sint.nat i)).length = d.length := by
      rw [List.length_drop, Hg.2.2.1, ← Hlenp.1]; omega
    have hz : List.drop d.length (List.drop (sint.nat i) all2) = [] :=
      List.drop_eq_nil_of_le (by omega)
    rw [hz, List.append_nil, Hdl, List.take_of_length_le (l := d) (Nat.le_refl _)]
    have hil : (all2.take (sint.nat i)).length = sint.nat i := by
      rw [List.length_take]; have := Hg.2.2.1; omega
    ihave Hbuf := ownSlice_combine (GF := GF) (V := w8) i bb2 (DFrac.own 1) _ d (W64 0) bb2.len
      ⟨by rw [hil, show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero], by decide, Hb.1, Hb.2.1⟩ $$ Hbuf1 Hbuf2
    ihave Hbuf := ownSlice_trivial_slice_2 $$ Hbuf
    have Hkd : k = W64 (d.length : Int) := by
      have hdb : (d.length : Int) ≤ 2 ^ 47 := by
        have := Hpb; unfold maxAddr at this; rw [Hlenp.1]; word
      apply BitVec.eq_of_toInt_eq; change sint.Z k = sint.Z (W64 _); rw [Hk]; word
    rw [Hkd]
    iapply HΦ
    iframe Hp
    iexists ⟨bb2, off2, lr2⟩, all2.take (sint.nat i) ++ d
    iframe Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn2
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    refine ⟨Hg.1, by simp only [List.length_append, hil]; word, ?_⟩
    rw [List.drop_append_of_le_length (by rw [hil]; word), Hg.2.2.2]

end proof

end Perennial
