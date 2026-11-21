/-
The proof of `strconv.FormatInt`.
-/
module

public import Perennial.Spec.strconv.FormatInt
public import Perennial.Spec.internal.strconv.FormatInt

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

theorem strconv.FormatInt.wp_proof
    (wp_FormatInt : internal.strconv.FormatInt.spec (GF := GF) (hG := hG)) :
    strconv.FormatInt.spec (GF := GF) (hG := hG) := by
  intro i base hb1 hb2
  wp_start
  wp_auto
  wp_apply wp_FormatInt i base hb1 hb2
  iapply HΦ
  itrivial

end proof

end Perennial
