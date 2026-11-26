/-
The proof of `math.Pow` (`pow`: no assembly on amd64).
-/
module

public import Perennial.Spec.math.Pow
public import Perennial.Spec.math.pow_

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

theorem math.Pow.wp_proof
    (wp_pow : math.pow.spec (GF := GF) (hG := hG)) :
    math.Pow.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_apply wp_pow as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
