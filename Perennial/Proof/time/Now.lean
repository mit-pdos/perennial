/-
`time.Now`'s spec, assumed.
-/
module

public import Perennial.Spec.time.Now

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

/-- Axiom: `Now` reads the clock through the `go:linkname` `runtimeNow`. -/
axiom time.Now.wp_proof : time.Now.spec (GF := GF) (hG := hG)

end proof

end Perennial
