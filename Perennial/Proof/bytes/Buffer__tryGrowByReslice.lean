/-
The proof of `bytes.Buffer.tryGrowByReslice`.
-/
module

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

theorem bytes.Buffer.tryGrowByReslice.wp_proof :
    bytes.Buffer.tryGrowByReslice.spec (GF := GF) (hG := hG) := by
  intro l b all n
  wp_start as ⟨Hl, Hbuf, Hcap, %Hpre⟩
  ihave %Hlen := ownSlice_len $$ Hbuf
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨bb, off, lr⟩ := b
  simp only at Hpre Hlen Hwf ⊢
  iStructNamed Hl
  wp_auto
  wp_if_destruct
  · -- `n` more bytes fit: `b.buf = b.buf[:l+n]`
    have Hn : sint.Z (bb.len + n) = sint.Z bb.len + sint.Z n := by word
    have Hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) ≤ sint.Z (bb.len + n) ∧
        sint.Z (bb.len + n) ≤ sint.Z bb.cap := ⟨by decide, by word, by word⟩
    simp only [Hb, _root_.and_self, ↓reduceIte]
    icases ownSlice_reslice bb all (bb.len + n) ⟨by word, by word⟩ $$ [$Hbuf $Hcap]
      with ⟨%all', Hbuf, Hcap, %Htk⟩
    ihave %Hlen' := ownSlice_len $$ Hbuf
    wp_auto
    iapply HΦ
    simp only [↓reduceIte]
    unfold bytes.bufferGrown
    iexists ⟨slice.slice bb w8 (W64 0) (bb.len + n), off, lr⟩, all'
    iframe Hbuf Hcap
    isplitl
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    ipureintro
    simp only [slice.slice] at Hlen' ⊢
    have Hl1 : all'.length = sint.nat bb.len + sint.nat n := by
      rw [Hlen'.1]; word
    refine ⟨Hpre.2.1, by word, Hl1, ?_⟩
    rw [← Hlen.1, Htk, List.take_of_length_le (by rw [Hlen.1]; word)]
  · iapply HΦ
    simp only [Bool.false_eq_true, ↓reduceIte]
    iframe Hbuf Hcap
    isplitr
    · ipureintro; exact ⟨by word, trivial⟩
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end Perennial
