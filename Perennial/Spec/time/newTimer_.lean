/-
`time.newTimer`'s spec.
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

/-- The model of the runtime's `newTimer(when, 0, f, arg, cp)` (one firing): for a positive
`when` (the runtime throws otherwise) and a callback `f(arg, seq, delay)` that runs from `P`, a
new `*Timer` with `initTimer` set, one of the runtime's timers (`runtimeTimerCell`), whose firing
runs from `P` (`timerFiring`; it runs once, with the caller's `P`). -/
abbrev time.newTimer.spec : Prop :=
  ∀ (w : w64) (f : GoFunc) (arg : GoInterface) (cp : Loc) (P : IProp GF),
    {{ ⌜0 < sint.Z w⌝ ∗ timerCallback f arg P ∗ P }}
      (App (App (App (App (App (Val (@! time.newTimer)) (Val #w)) (Val #(W64 0))) (Val #f))
        (Val #arg)) (Val #cp))
    {{ (t : Loc) (fire : GoFunc), RET #t; (∃ c : Loc, structFieldRef time.Timer go!"C" t ↦ c) ∗
        structFieldRef time.Timer go!"initTimer" t ↦□ true ∗ runtimeTimerCell t fire ∗
        timerFiring fire P }}

end spec

end Perennial
