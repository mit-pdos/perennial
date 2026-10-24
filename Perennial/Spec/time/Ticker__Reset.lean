/-
`time.Ticker.Reset`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `(*Ticker).Reset(d)` (trusted model, `TrustedCode/time.lean`): for a ticker made by
`NewTicker` (`isTicker`, which rules out Go's panic on an uninitialized ticker) and a positive
`d` (Go panics otherwise). -/
abbrev time.Ticker.Reset.spec : Prop :=
  ∀ (t : Loc) (d : time.Duration),
    {{ ⌜0 < sint.Z d⌝ ∗ ∃ (ch : Loc) (γ : ChanNames), isTicker (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Ticker.ty @!! go!"Reset")) (Val #d))
    {{ RET #(); True }}

end spec

end Perennial
