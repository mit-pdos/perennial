/-
The proof of `bytes.Buffer.String`.
-/
module

public import Perennial.Spec.bytes.Buffer__String

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

theorem bytes.Buffer.String.wp_proof :
    bytes.Buffer.String.spec (GF := GF) (hG := hG) := by
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
  wp_if_destruct
  · exact absurd rfl Hnn
  have Hb : 0 ≤ sint.Z off ∧ sint.Z off ≤ sint.Z bb.len ∧ sint.Z bb.len ≤ sint.Z bb.cap :=
    ⟨Hoff.1, by word, Hwf.2⟩
  simp only [Hb, _root_.and_self, ↓reduceIte]
  icases (ownSlice_split_all off bb _ _ ⟨Hoff.1, by word⟩).1 $$ Hbuf with ⟨Hbuf1, Hbuf2⟩
  wp_apply wp_bytes_to_string $$ Hbuf2 as Hbuf2
  ihave Hbuf := ownSlice_combine (GF := GF) (V := w8) off bb (DFrac.own 1) _ _ (W64 0) bb.len
      ⟨by rw [List.length_take]; word, by decide, Hoff.1, by word⟩ $$ Hbuf1 Hbuf2
  ihave Hbuf := ownSlice_trivial_slice_2 $$ Hbuf
  rw [← Hoff.2.2]
  iapply HΦ
  iexists ⟨bb, off, lr⟩, all
  iframe Hcap
  isplitl [buf off lastRead]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  isplitl [Hbuf]
  · rw [Hoff.2.2, List.take_append_drop]; iexact Hbuf
  ipureintro
  exact Hoff

end proof

end Perennial
