/-
`time.Timer.Stop`'s spec, assumed.
-/
module

public import Perennial.Spec.time.Timer__Stop

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

/-- Axiom: `Stop` is not translated (it calls the runtime's `stopTimer`). -/
axiom time.Timer.Stop.wp_proof : time.Timer.Stop.spec (GF := GF) (hG := hG)

end proof

end Perennial
