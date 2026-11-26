/-
The proof of `math.ceil`.
-/
module

public import Perennial.Spec.math.ceil_
public import Perennial.Spec.math.Floor
public import Perennial.Golang.Theory.Float

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

theorem math.ceil.wp_proof
    (wp_Floor : math.Floor.spec (GF := GF) (hG := hG)) :
    math.ceil.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_float64_neg as %_ -
  (try wp_auto)
  wp_apply wp_Floor as %_ -
  (try wp_auto)
  wp_apply wp_float64_neg as %_ -
  (try wp_auto)
  wp_end

end proof

end Perennial
