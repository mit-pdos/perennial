/-
The proof of `cmp.isNaN` (at `uint64`).
-/
module

public import Perennial.Spec.cmp.isNaN

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cmp.Assumptions]

theorem cmp.isNaN.wp_proof : cmp.isNaN.spec (GF := GF) (hG := hG) := by
  constructor
  · intro x
    wp_start
    wp_auto
    wp_end
  · intro x
    wp_start
    wp_auto
    wp_end

end proof

end Perennial
