/-
The proof of `runtime.Gosched`.
-/
module

public import Perennial.Spec.runtime.Gosched

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.Gosched.wp_proof :
    runtime.Gosched.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_end

end proof

end Perennial
