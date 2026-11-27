/-
The proof of `strconv.NumError.Error`.
-/
module

public import Perennial.Spec.strconv.NumError__Error
public import Perennial.Spec.strconv.Quote

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

theorem strconv.NumError.Error.wp_proof
    (wp_Quote : strconv.Quote.spec (GF := GF) (hG := hG)) :
    strconv.NumError.Error.spec (GF := GF) (hG := hG) := by
  intro l v dq ei hErr
  wp_start as ⟨Hl, HE⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hl
  obtain ⟨fn, s, e⟩ := v
  simp only at hErr
  subst hErr
  iStructNamed Hl
  wp_auto
  wp_apply wp_Quote as %q -
  iunfold strconv.errorReturns at HE
  wp_bind (App (Val #(methods ei.ty go!"Error" ei.v)) (Val #()))
  iapply HE
  inext
  iintro %m
  wp_auto
  iapply HΦ
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe

end proof

end Perennial
