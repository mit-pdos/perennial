/-
The proof of `strings.Builder.copyCheck`.
-/
module

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

theorem strings.Builder.copyCheck.wp_proof :
    strings.Builder.copyCheck.spec (GF := GF) (hG := hG) := by
  intro l b
  wp_start as ⟨Hl, %Haddr⟩
  rw [show go.GoType.Named go!"strings.Builder" [] = strings.Builder.ty by with_unfolding_all rfl]
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨addr, buf⟩ := b
  simp only at Haddr ⊢
  iStructNamed Hl
  wp_auto
  wp_if_destruct
  · -- nil: `b.addr = b` (the model's `copyCheck`)
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · -- `b.addr == b`: no panic
    have Hl : addr = l := Haddr.resolve_right Hif
    subst Hl
    wp_auto
    iapply HΦ
    iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end proof

end Perennial
