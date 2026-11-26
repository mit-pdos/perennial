/-
The proof of `math.archExp`, over its Go model (`goose/model/overlay/math`: some `float64`).
-/
module

public import Perennial.Spec.math.archExp
public import Perennial.Spec.internal.gomodel.ChooseUint64
public import Perennial.Spec.math.Float64frombits

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

theorem math.archExp.wp_proof
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_Float64frombits : math.Float64frombits.spec (GF := GF) (hG := hG)) :
    math.archExp.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_ChooseUint64 as %_ -
  (try wp_auto)
  wp_apply wp_Float64frombits
  (try wp_auto)
  wp_end

end proof

end Perennial
