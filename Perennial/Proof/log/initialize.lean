/-
The proof of `log.initialize'` (unfinished).
-/
module

public import Perennial.Spec.log.initialize

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : log.Assumptions]

theorem log.initialize'.wp_proof :
    log.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  -- Unprovable: `std'init` and `bufferPool'init` are opaque (axioms in Perennial/Code/log.lean).
  sorry

end proof

end Perennial
