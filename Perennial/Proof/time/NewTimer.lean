/-
`time.NewTimer`'s spec, assumed.
-/
module

public import Perennial.Spec.time.NewTimer

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

/-- Axiom: `NewTimer` is not translated (the runtime's timers are not modelled). -/
axiom time.NewTimer.wp_proof : time.NewTimer.spec (GF := GF) (hG := hG)

end proof

end Perennial
