/-
The proof of `strings.Builder.WriteString`.
-/
module

public import Perennial.Spec.strings.Builder__WriteString
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

theorem strings.Builder.WriteString.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG)) :
    strings.Builder.WriteString.spec (GF := GF) (hG := hG) := by
  intro l s x
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
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append_dfrac (V := w8) buf s dq sl x (DFrac.own 1) $$ [Hbuf Hcap Hsl]
    as %buf' ⟨Hbuf, Hcap, -⟩
  · iframe; ipureintro; exact Hinv.1
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
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
