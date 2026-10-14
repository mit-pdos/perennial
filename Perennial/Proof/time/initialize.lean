/-
The proof of `time.initialize'` (unfinished: `sorry`).
-/
module

public import Perennial.Spec.time.initialize

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

theorem time.initialize'.wp_proof :
    time.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  -- Unprovable: `UTC'init`, `Local'init`, ... are opaque (axioms in Perennial/Code/time.lean).
  sorry

end proof

end Perennial
