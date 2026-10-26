/-
`time.Ticker.Stop`'s spec.
-/
module

public import Perennial.Proof.time.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `(*Ticker).Stop()` (trusted model, `TrustedCode/time.lean`): for a ticker made by
`NewTicker` (`isTicker`). The ticker's channel may still yield some time afterwards (Go's
delivers none; the specs of the channel say nothing of when values arrive). -/
abbrev time.Ticker.Stop.spec : Prop :=
  ∀ (t : Loc),
    {{ ∃ (ch : Loc) (γ : ChanNames), isTicker (GF := GF) t ch γ }}
      (App (Val (t @!! go.GoType.PointerType time.Ticker.ty @!! go!"Stop")) (Val #()))
    {{ RET #(); True }}

end spec

end Perennial
