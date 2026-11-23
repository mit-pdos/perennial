/-
The proof of `strconv.FormatUint`.
-/
module

public import Perennial.Spec.strconv.FormatUint
public import Perennial.Spec.internal.strconv.FormatUint

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

theorem strconv.FormatUint.wp_proof
    (wp_FormatUint : internal.strconv.FormatUint.spec (GF := GF) (hG := hG)) :
    strconv.FormatUint.spec (GF := GF) (hG := hG) := by
  intro i base hb1 hb2
  wp_start
  wp_auto
  wp_apply wp_FormatUint i base hb1 hb2
  iapply HΦ
  itrivial

end proof

end Perennial
