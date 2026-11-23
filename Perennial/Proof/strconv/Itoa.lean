/-
The proof of `strconv.Itoa`.
-/
module

public import Perennial.Spec.strconv.Itoa
public import Perennial.Spec.internal.strconv.Itoa

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

theorem strconv.Itoa.wp_proof
    (wp_Itoa : internal.strconv.Itoa.spec (GF := GF) (hG := hG)) :
    strconv.Itoa.spec (GF := GF) (hG := hG) := by
  intro i
  wp_start
  wp_auto
  wp_apply wp_Itoa i
  iapply HΦ
  itrivial

end proof

end Perennial
