/-
The proof of `math/rand.seedrand`.
-/
module

public import Perennial.Spec.math.rand.seedrand

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

theorem math.rand.seedrand.wp_proof : math.rand.seedrand.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_if_destruct <;> (try wp_auto); all_goals (iapply HΦ; itrivial)

end proof

end Perennial
