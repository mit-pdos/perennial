/-
`time.startTimer`'s spec.
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

/-- `startTimer(fire, when, period)`: arms a timer, a goroutine that fires (`fire()`) once
(`period = 0`, from the caller's `P`) or again and again (any `period`, from a persistent `P`). -/
abbrev time.startTimer.spec : Prop :=
  ∀ (fire : GoFunc) (w p : w64) (P : IProp GF),
    {{ timerFiring fire P ∗ ((⌜p = W64 0⌝ ∗ P) ∨ □ P) }}
      (App (App (App (Val (@! time.startTimer)) (Val #fire)) (Val #w)) (Val #p))
    {{ RET #(); True }}

end spec

end Perennial
