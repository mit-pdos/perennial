/-
`time.runtimeTimerFire`'s spec.
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

/-- `runtimeTimerFire(p)`, a primitive stub of the model (`TrustedCode/time.lean`): the firing
held by the runtime's state of the timer at `p`, which only `newRuntimeTimer` and
`newRuntimeTicker` make (`runtimeTimerCell`). -/
abbrev time.runtimeTimerFire.spec : Prop :=
  ∀ (t : Loc) (fire : GoFunc),
    {{ runtimeTimerCell (GF := GF) t fire }}
      (App (Val (@! time.runtimeTimerFire)) (Val #t))
    {{ RET #fire; True }}

end spec

end Perennial
