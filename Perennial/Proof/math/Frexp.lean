/-
The proof of `math.Frexp` (`frexp`: no assembly on amd64).
-/
module

public import Perennial.Spec.math.Frexp
public import Perennial.Spec.math.frexp_

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

theorem math.Frexp.wp_proof
    (wp_frexp : math.frexp.spec (GF := GF) (hG := hG)) :
    math.Frexp.spec (GF := GF) (hG := hG) := by
  intro f
  wp_start
  wp_auto
  wp_apply wp_frexp as %_ %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
