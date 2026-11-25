/-
`time.resetTimer`'s spec.
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

/-- The model of the runtime's `resetTimer(t, when, period)`: as `resetTimerAt`. -/
abbrev time.resetTimer.spec : Prop :=
  ∀ (t : Loc) (w p : w64),
    {{ ⌜0 < sint.Z w ∧ 0 ≤ sint.Z p⌝ ∗
        ∃ fire : GoFunc, runtimeTimerCell (GF := GF) t fire ∗ timerFiring fire iprop(True) }}
      (App (App (App (Val (@! time.resetTimer)) (Val #t)) (Val #w)) (Val #p))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
