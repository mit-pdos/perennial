/-
The proof of `time.runtimeNow`.
-/
module

public import Perennial.Spec.time.runtimeNow

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

theorem time.runtimeNow.wp_proof :
    time.runtimeNow.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %sec -
  wp_apply wp_ArbitraryInt as %nsec -
  wp_apply wp_ArbitraryInt as %mono -
  wp_end

end proof

end Perennial
