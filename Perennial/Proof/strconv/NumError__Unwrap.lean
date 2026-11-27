/-
The proof of `strconv.NumError.Unwrap`.
-/
module

public import Perennial.Spec.strconv.NumError__Unwrap

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

theorem strconv.NumError.Unwrap.wp_proof :
    strconv.NumError.Unwrap.spec (GF := GF) (hG := hG) := by
  intro l v dq
  wp_start as Hl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨fn, s, e⟩ := v
  iStructNamed Hl
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
