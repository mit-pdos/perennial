/-
The proof of `math/rand.runtime_rand`.
-/
module

public import Perennial.Spec.math.rand.runtime_rand

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.runtime_rand.wp_proof :
    math.rand.runtime_rand.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %y -
  wp_end

end proof

end Perennial
