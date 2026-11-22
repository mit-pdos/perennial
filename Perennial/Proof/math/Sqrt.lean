/-
The proof of `math.Sqrt`.
-/
module

public import Perennial.Spec.math.Sqrt
public import Perennial.Spec.math.sqrt_

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

theorem math.Sqrt.wp_proof
    (wp_sqrt : math.sqrt.spec (GF := GF) (hG := hG)) :
    math.Sqrt.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_sqrt as %y -
  (try wp_auto)
  wp_end

end proof

end Perennial
