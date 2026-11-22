/-
The proof of `strings.Builder.Reset`.
-/
module

public import Perennial.Spec.strings.Builder__Reset

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

theorem strings.Builder.Reset.wp_proof :
    strings.Builder.Reset.spec (GF := GF) (hG := hG) := by
  intro l s
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%b, %dq, Hl, -, -, %Hinv⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨addr, buf⟩ := b
  iStructNamed Hl
  wp_auto
  iapply HΦ
  iexists ⟨null, slice.nil⟩, DFrac.own 1
  isplitl [addr buf]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  isplitr
  · iapply ownSlice_nil
  isplitr
  · iapply ownSliceCap_nil
  ipureintro; exact ⟨DFrac.valid_own_one, Or.inr ⟨rfl, rfl⟩⟩

end proof

end Perennial
