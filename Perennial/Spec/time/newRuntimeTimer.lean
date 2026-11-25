/-
`time.newRuntimeTimer`'s spec.
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

/-- `newRuntimeTimer(fire)`, a primitive stub of the model (`TrustedCode/time.lean`): a new
`*Timer` with `initTimer` set, whose `C` the caller may still set, and the runtime's state of the
timer, holding `fire` (`runtimeTimerCell`). -/
abbrev time.newRuntimeTimer.spec : Prop :=
  ∀ (fire : GoFunc),
    {{ (True : IProp GF) }}
      (App (Val (@! time.newRuntimeTimer)) (Val #fire))
    {{ (t : Loc), RET #t; (∃ c : Loc, structFieldRef time.Timer go!"C" t ↦ c) ∗
        structFieldRef time.Timer go!"initTimer" t ↦□ true ∗ runtimeTimerCell t fire }}

end spec

end Perennial
