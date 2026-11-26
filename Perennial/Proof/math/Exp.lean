/-
The proof of `math.Exp` (`archExp` on amd64).
-/
module

public import Perennial.Spec.math.Exp
public import Perennial.Spec.math.archExp

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

theorem math.Exp.wp_proof
    (wp_archExp : math.archExp.spec (GF := GF) (hG := hG)) :
    math.Exp.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_archExp as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
