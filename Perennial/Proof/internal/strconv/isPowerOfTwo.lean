/-
The proof of `internal.strconv.isPowerOfTwo`.
-/
module

public import Perennial.Spec.internal.strconv.isPowerOfTwo

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.strconv.Assumptions]

theorem internal.strconv.isPowerOfTwo.wp_proof :
    internal.strconv.isPowerOfTwo.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_end

end proof

end Perennial
