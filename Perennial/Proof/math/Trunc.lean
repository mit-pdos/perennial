/-
The proof of `math.Trunc` (`archTrunc` on amd64).
-/
module

public import Perennial.Spec.math.Trunc
public import Perennial.Spec.math.archTrunc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.Assumptions]

theorem math.Trunc.wp_proof
    (wp_archTrunc : math.archTrunc.spec (GF := GF) (hG := hG)) :
    math.Trunc.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_archTrunc as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
