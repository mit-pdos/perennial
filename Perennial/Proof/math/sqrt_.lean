/-
The proof of `math.sqrt`, over its trusted model (`TrustedCode/math.lean`: an arbitrary bit
pattern, as gc compiles `sqrt` to the square-root instruction).
-/
module

public import Perennial.Spec.math.sqrt_

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

theorem math.sqrt.wp_proof :
    math.sqrt.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_apply wp_ArbitraryInt as %y -
  wp_end

end proof

end Perennial
