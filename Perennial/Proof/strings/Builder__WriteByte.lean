/-
The proof of `strings.Builder.WriteByte`.
-/
module

public import Perennial.Spec.strings.Builder__WriteByte
public import Perennial.Spec.strings.Builder__copyCheck

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.Builder.WriteByte.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG)) :
    strings.Builder.WriteByte.spec (GF := GF) (hG := hG) := by
  intro l s c
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%b, %dq, Hl, Hbuf, Hcap, %Hinv⟩
  wp_auto
  wp_apply wp_copyCheck $$ [Hl] as Hl
  · iframe Hl; ipureintro
    rcases Hinv.2 with h | ⟨h, -⟩ <;> simp [h]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨addr, buf⟩ := b
  simp only at Hinv ⊢
  iStructNamed Hl
  wp_apply wp_slice_literal (V := w8) (t := go.byte) [c]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append_dfrac (V := w8) buf s dq _ [c] (DFrac.own 1) $$ [Hbuf Hcap Hsl]
    as %buf' ⟨Hbuf, Hcap, -⟩
  · iframe; ipureintro; exact Hinv.1
  iapply HΦ
  iexists ⟨l, buf'⟩, dq
  iframe Hbuf Hcap
  isplitl [addr buf]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro; exact ⟨Hinv.1, Or.inl rfl⟩

end proof

end Perennial
