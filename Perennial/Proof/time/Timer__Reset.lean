/-
`time.Timer.Reset`'s spec, assumed.
-/
module

public import Perennial.Spec.time.Timer__Reset

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Axiom: `Reset` is not translated (it calls the runtime's `resetTimer`). -/
axiom time.Timer.Reset.wp_proof : time.Timer.Reset.spec (GF := GF) (hG := hG)

end proof

end Perennial
