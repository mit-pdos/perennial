/-
The proof of `strings.Builder.Write`.
-/
module

public import Perennial.Spec.strings.Builder__Write
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

theorem strings.Builder.Write.wp_proof
    (wp_copyCheck : strings.Builder.copyCheck.spec (GF := GF) (hG := hG)) :
    strings.Builder.Write.spec (GF := GF) (hG := hG) := by
  intro l s p bs dp
  wp_start as ⟨Hown, Hp⟩
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
  ihave %Hplen := ownSlice_len $$ Hp
  wp_apply wp_slice_append_dfrac (V := w8) buf s dq p bs dp $$ [Hbuf Hcap Hp]
    as %buf' ⟨Hbuf, Hcap, Hp⟩
  · iframe; ipureintro; exact Hinv.1
  rw [show p.len = W64 (bs.length : Int) by word]
  iapply HΦ
  iframe Hp
  iexists ⟨l, buf'⟩, dq
  iframe Hbuf Hcap
  isplitl [addr buf]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro; exact ⟨Hinv.1, Or.inl rfl⟩

end proof

end Perennial
