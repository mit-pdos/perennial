/-
The proof of `math.bits.Mul`.
-/
module

public import Perennial.Spec.math.bits.Mul
public import Perennial.Spec.math.bits.Mul64

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.bits.Assumptions]

theorem math.bits.Mul.wp_proof
    (wp_Mul64 : math.bits.Mul64.spec (GF := GF) (hG := hG)) :
    math.bits.Mul.spec (GF := GF) (hG := hG) := by
  intro x y
  wp_start
  wp_auto
  wp_apply wp_Mul64
  wp_end

end proof

end Perennial
