/-
The proof of `math.Ldexp` (`ldexp`: no assembly on amd64).
-/
module

public import Perennial.Spec.math.Ldexp
public import Perennial.Spec.math.ldexp_

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

theorem math.Ldexp.wp_proof
    (wp_ldexp : math.ldexp.spec (GF := GF) (hG := hG)) :
    math.Ldexp.spec (GF := GF) (hG := hG) := by
  intro frac exp
  wp_start
  wp_auto
  wp_apply wp_ldexp as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
