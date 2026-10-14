/-
The proof of `time.runtimeIsBubbled`.
-/
module

public import Perennial.Spec.time.runtimeIsBubbled

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

theorem time.runtimeIsBubbled.wp_proof :
    time.runtimeIsBubbled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_ArbitraryInt as %x -
  wp_end

end proof

end Perennial
