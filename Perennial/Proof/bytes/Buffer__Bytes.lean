/-
The proof of `bytes.Buffer.Bytes`.
-/
module

public import Perennial.Spec.bytes.Buffer__Bytes

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

theorem bytes.Buffer.Bytes.wp_proof :
    bytes.Buffer.Bytes.spec (GF := GF) (hG := hG) := by
  intro l bs
  wp_start as Hown
  unfold bytes.ownBuffer
  icases Hown with ⟨%b, %all, Hl, Hbuf, Hcap, %Hoff⟩
  ihave %Hlen := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hoff Hlen Hwf ⊢
  iStructNamed Hl
  wp_auto
  have Hb : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z bb.len ∧ sint.Z bb.len ≤ sint.Z bb.cap :=
    ⟨Hoff.1, by word, Hwf.2⟩
  simp only [Hb, _root_.and_self, ↓reduceIte]
  icases (ownSlice_split_all off bb _ _ ⟨Hoff.1, by word⟩).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
  wp_auto
  iapply HΦ
  rw [← Hoff.2.2]
  iframe Hbuf2
  iintro %bs' Hbuf2
  ihave %Hlen' := ownSlice_len $$ Hbuf2
  ihave Hbuf := ownSlice_combine (GF := GF) (V := w8) off bb (DFrac.own 1) _ bs' (W64 0) bb.len
      ⟨by rw [List.length_take]; word, by decide, Hoff.1, by word⟩ $$ Hbuf1 Hbuf2
  ihave Hbuf := ownSlice_trivial_slice_2 $$ Hbuf
  iexists ⟨bb, off, lr⟩, all.take (sint.nat off) ++ bs'
  iframe Hbuf Hcap
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro
  simp only [List.length_append, List.length_take]
  refine ⟨Hoff.1, by omega, ?_⟩
  rw [List.drop_append_of_le_length (by rw [List.length_take]; omega)]
  simp

end proof

end Perennial
