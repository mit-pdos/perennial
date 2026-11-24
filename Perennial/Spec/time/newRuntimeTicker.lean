/-
`time.newRuntimeTicker`'s spec.
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

/-- `newRuntimeTicker(fire)`, a primitive stub of the model (`TrustedCode/time.lean`): a new
`*Ticker` with `initTicker` set, whose `C` the caller may still set, and the runtime's state of the
timer, holding `fire` (`runtimeTimerCell`). -/
abbrev time.newRuntimeTicker.spec : Prop :=
  ∀ (fire : GoFunc),
    {{ (True : IProp GF) }}
      (App (Val (@! time.newRuntimeTicker)) (Val #fire))
    {{ (t : Loc), RET #t; (∃ c : Loc, structFieldRef time.Ticker go!"C" t ↦ c) ∗
        structFieldRef time.Ticker go!"initTicker" t ↦□ true ∗ runtimeTimerCell t fire }}

end spec

end Perennial
