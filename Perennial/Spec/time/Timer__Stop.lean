/-
`time.Timer.Stop`'s spec.
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

/-- Spec of `(*Timer).Stop()`: some `bool`, for a timer made by `NewTimer` (`isTimer`) or by
`AfterFunc` (`isFuncTimer`). Both say that `t` is one of the runtime's timers
(`isRuntimeTimer`), which a `Timer` the program made, such as a copy, is not.

For a timer made by `AfterFunc`: Go's `Stop` checks `initTimer` (set by the runtime's
`newTimer`) and calls the runtime's `stopTimer`, which stops the timer if it has not fired (so
that `f` does not run) and reports whether it did; the model of `newTimer` runs `f` regardless,
so the result says nothing the proof can use.

`Results.lean` derives the two cases from this spec, as `Timer.wp_Stop_timer` and
`Timer.wp_Stop_func`. -/
abbrev time.Timer.Stop.spec : Prop :=
  ∀ (t : Loc),
    {{ iprop((∃ (ch : Loc) (γ : ChanNames), isTimer (GF := GF) t ch γ) ∨ isFuncTimer (GF := GF) t) }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
