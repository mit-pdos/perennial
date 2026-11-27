/-
The proof of `math.Inf`.
-/
module

public import Perennial.Spec.math.Inf
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

theorem math.Inf.wp_proof
    (wp_Float64frombits : math.Float64frombits.spec (GF := GF) (hG := hG)) :
    math.Inf.spec (GF := GF) (hG := hG) := by
  intro sign
  wp_start
  (try wp_auto)
  repeat' (first
    | wp_end
    | (wp_apply wp_Float64frombits; (try wp_auto))
    | wp_auto
    | wp_if_destruct)

end proof

end Perennial
