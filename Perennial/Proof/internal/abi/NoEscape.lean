/-
The proof of `internal.abi.NoEscape`.
-/
module

public import Perennial.Spec.internal.abi.NoEscape

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : internal.abi.Assumptions]

/-- Proved from the model of `NoEscape` (`Perennial/TrustedCode/internal/abi.lean`). -/
theorem internal.abi.NoEscape.wp_proof :
    internal.abi.NoEscape.spec (GF := GF) (hG := hG) := fun p => by
  wp_start
  wp_end

end proof

end Perennial
