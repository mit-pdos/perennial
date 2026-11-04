/-
`time.Ticker.Stop`'s spec, assumed.
-/
module

public import Perennial.Spec.time.Ticker__Stop

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Axiom: `Ticker.Stop` is not translated (Go reinterprets the runtime's `*Timer` as a `*Ticker`
through `unsafe.Pointer`; the runtime's timers are not modelled). -/
axiom time.Ticker.Stop.wp_proof : time.Ticker.Stop.spec (GF := GF) (hG := hG)

end proof

end Perennial
