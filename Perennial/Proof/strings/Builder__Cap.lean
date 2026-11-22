/-
The proof of `strings.Builder.Cap`.
-/
module

public import Perennial.Spec.strings.Builder__Cap

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

theorem strings.Builder.Cap.wp_proof :
    strings.Builder.Cap.spec (GF := GF) (hG := hG) := by
  intro l s
  wp_start as Hown
  unfold strings.ownBuilder
  icases Hown with ⟨%b, %dq, Hl, Hbuf, Hcap, %Hinv⟩
  ihave %Hlen := ownSlice_len $$ Hbuf
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨addr, buf⟩ := b
  simp only at Hinv Hlen ⊢
  iStructNamed Hl
  ihave %Hwf := ownSlice_wf $$ Hbuf
  ihave %Hcw := ownSliceCap_wf $$ Hcap
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; word
  iexists ⟨addr, buf⟩, dq
  iframe Hbuf Hcap
  isplitl [addr buf]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ipureintro; exact Hinv

end proof

end Perennial
