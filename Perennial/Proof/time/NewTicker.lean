/-
`time.NewTicker`'s spec, assumed.
-/
module

public import Perennial.Spec.time.NewTicker

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

/-- Axiom: `NewTicker` is not translated (Go reinterprets the runtime's `*Timer` as a `*Ticker`
through `unsafe.Pointer`; the runtime's timers are not modelled). -/
axiom time.NewTicker.wp_proof : time.NewTicker.spec (GF := GF) (hG := hG)

end proof

end Perennial
