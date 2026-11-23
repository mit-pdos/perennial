/-
The proof of `internal.strconv.Itoa`.
-/
module

public import Perennial.Spec.internal.strconv.Itoa
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
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.Itoa.wp_proof
    (wp_FormatInt : internal.strconv.FormatInt.spec (GF := GF) (hG := hG)) :
    internal.strconv.Itoa.spec (GF := GF) (hG := hG) := by
  intro i
  wp_start
  wp_auto
  wp_apply wp_FormatInt i (W64 10) (by word) (by word)
  iapply HΦ
  itrivial

end proof

end Perennial
