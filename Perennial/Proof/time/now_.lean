/-
The proof of `time.now`.
-/
module

public import Perennial.Spec.time.now_

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Over the primitive stub `now.impl` (`TrustedCode/time.lean`). -/
theorem time.now.wp_proof : time.now.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %x1 -
  wp_apply wp_ArbitraryInt as %x2 -
  wp_apply wp_ArbitraryInt as %x3 -
  wp_end

end proof

end Perennial
