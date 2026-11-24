/-
`time.timerFunc`'s spec.
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

/-- `timerFunc(f, arg)`: a timer's firing, which calls `f(arg, seq, delay)` for some `seq` and
`delay`: from the callback's triple (`timerCallback f arg P`), the firing's
(`timerFiring fire P`). -/
abbrev time.timerFunc.spec : Prop :=
  ∀ (f : GoFunc) (arg : GoInterface) (P : IProp GF),
    {{ timerCallback f arg P }}
      (App (App (Val (@! time.timerFunc)) (Val #f)) (Val #arg))
    {{ (fire : GoFunc), RET #fire; timerFiring fire P }}

end spec

end Perennial
