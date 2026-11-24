/-
`time.stopTimer`'s spec.
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

/-- The model of the runtime's `stopTimer(t)`: some `bool`, for one of the runtime's timers
(`isRuntimeTimer`). -/
abbrev time.stopTimer.spec : Prop :=
  ∀ (t : Loc),
    {{ isRuntimeTimer (GF := GF) t }}
      (App (Val (@! time.stopTimer)) (Val #t))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
