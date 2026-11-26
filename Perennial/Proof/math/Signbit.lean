/-
The proof of `math.Signbit`.
-/
module

public import Perennial.Spec.math.Signbit
public import Perennial.Spec.math.Float64bits

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

theorem math.Signbit.wp_proof
    (wp_Float64bits : math.Float64bits.spec (GF := GF) (hG := hG)) :
    math.Signbit.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_Float64bits
  (try wp_auto)
  wp_end

end proof

end Perennial
