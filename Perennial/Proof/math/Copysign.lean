/-
The proof of `math.Copysign`.
-/
module

public import Perennial.Spec.math.Copysign
public import Perennial.Spec.math.Float64bits
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

theorem math.Copysign.wp_proof
    (wp_Float64bits : math.Float64bits.spec (GF := GF) (hG := hG))
    (wp_Float64frombits : math.Float64frombits.spec (GF := GF) (hG := hG)) :
    math.Copysign.spec (GF := GF) (hG := hG) := by
  intro f sign
  wp_start
  wp_auto
  wp_apply wp_Float64bits
  (try wp_auto)
  wp_apply wp_Float64bits
  (try wp_auto)
  wp_apply wp_Float64frombits
  (try wp_auto)
  wp_end

end proof

end Perennial
