/-
The proof of `time.runtimeNano`.
-/
module

public import Perennial.Spec.time.runtimeNano

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

theorem time.runtimeNano.wp_proof :
    time.runtimeNano.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end proof

end Perennial
