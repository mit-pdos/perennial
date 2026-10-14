/-
The proof of `internal.synctest.Run`.
-/
module

public import Perennial.Spec.internal.synctest.Run

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.synctest.Assumptions]

theorem internal.synctest.Run.wp_proof :
    internal.synctest.Run.spec (GF := GF) (hG := hG) := by
  intro v
  wp_start as ⟨⟩

end proof

end Perennial
