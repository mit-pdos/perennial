/-
The proof of `math.bits.TrailingZeros`.
-/
module

public import Perennial.Spec.math.bits.TrailingZeros
public import Perennial.Spec.math.bits.TrailingZeros64

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

/-- A `uint` is 64 bits: `TrailingZeros64(uint64(x))`. -/
theorem math.bits.TrailingZeros.wp_proof
    (wp_TrailingZeros64 : math.bits.TrailingZeros64.spec (GF := GF) (hG := hG)) :
    math.bits.TrailingZeros.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_apply wp_TrailingZeros64 as %r %Hr
  iapply HΦ
  ipureintro
  exact Hr
end proof

end Perennial
