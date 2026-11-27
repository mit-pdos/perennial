/-
The proof of `math.archCeil`, over its Go model (`goose/model/overlay/math`: `ceil(x)`, or some NaN).
-/
module

public import Perennial.Spec.math.archCeil
public import Perennial.Spec.math.chooseNaN
public import Perennial.Spec.math.ceil_

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

theorem math.archCeil.wp_proof
    (wp_chooseNaN : math.chooseNaN.spec (GF := GF) (hG := hG))
    (wp_ceil : math.ceil.spec (GF := GF) (hG := hG)) :
    math.archCeil.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_chooseNaN as %_ -; (try wp_auto))
    | (wp_apply wp_ceil as %_ -; (try wp_auto))
    | wp_auto
    | wp_if_destruct
    | (wp_if_bool; wp_if_destruct))

end proof

end Perennial
