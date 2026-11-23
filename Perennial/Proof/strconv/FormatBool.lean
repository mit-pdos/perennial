/-
The proof of `strconv.FormatBool`.
-/
module

public import Perennial.Spec.strconv.FormatBool
public import Perennial.Spec.internal.strconv.FormatBool

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

theorem strconv.FormatBool.wp_proof
    (wp_FormatBool : internal.strconv.FormatBool.spec (GF := GF) (hG := hG)) :
    strconv.FormatBool.spec (GF := GF) (hG := hG) := by
  intro b
  wp_start
  wp_auto
  wp_apply wp_FormatBool
  iapply HΦ; itrivial

end proof

end Perennial
