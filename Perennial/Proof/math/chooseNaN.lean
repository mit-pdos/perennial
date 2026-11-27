/-
The proof of `math.chooseNaN` (a declaration of the Go model, `goose/model/overlay/math`).
-/
module

public import Perennial.Spec.math.chooseNaN
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

theorem math.chooseNaN.wp_proof
    (wp_ChooseUint64 : internal.gomodel.ChooseUint64.spec (GF := GF) (hG := hG))
    (wp_Float64frombits : math.Float64frombits.spec (GF := GF) (hG := hG)) :
    math.chooseNaN.spec (GF := GF) (hG := hG) := by
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_ChooseUint64 as %_ -; (try wp_auto))
    | (wp_apply wp_Float64frombits; (try wp_auto))
    | wp_auto
    | wp_if_destruct)

end proof

end Perennial
