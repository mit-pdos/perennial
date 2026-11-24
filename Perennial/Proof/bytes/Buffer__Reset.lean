/-
The proof of `bytes.Buffer.Reset`.
-/
module

public import Perennial.Spec.bytes.Buffer__Reset

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

theorem bytes.Buffer.Reset.wp_proof :
    bytes.Buffer.Reset.spec (GF := GF) (hG := hG) := by
  intro l bs
  wp_start as Hown
  iunfold bytes.ownBuffer at Hown
  icases Hown with ⟨%b, %all, Hl, Hbuf, Hcap, %Hpre⟩
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hpre Hwf ⊢
  iStructNamed Hl
  wp_auto
  have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (W64 0) ∧
      sint.Z (W64 0) ≤ sint.Z bb.cap := ⟨by decide, by decide, by word⟩
  simp only [Hb, _root_.and_self, ↓reduceIte]
  icases bytes.ownSlice_reslice bb all (W64 0) ⟨by decide, by word⟩ $$ [$Hbuf $Hcap]
    with ⟨%all', Hbuf, Hcap, -⟩
  ihave %Hlen' := ownSlice_len $$ Hbuf
  wp_auto
  simp only [bytes.opInvalid]
  wp_auto
  iapply HΦ
  unfold bytes.ownBuffer
  iexists ⟨slice.slice bb w8 (W64 0) (W64 0), W64 0, W8 0⟩, all'
  iframe Hbuf Hcap
  isplitl
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro
  simp only [slice.slice] at Hlen' ⊢
  have Hl0 : all'.length = 0 := by rw [Hlen'.1]; word
  refine ⟨by decide, by simp, ?_⟩
  rw [List.length_eq_zero_iff.mp Hl0]; rfl

end proof

end Perennial
