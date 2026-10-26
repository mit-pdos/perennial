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

/-- Spec of `(*Timer).Stop()` (axiom): some `bool`, for a timer made by `NewTimer` (`isTimer`, whose
`newTimerMade t` a `Timer` the program made, such as a copy, does not have) or by `AfterFunc`
(`isFuncTimer`).

For a timer made by `AfterFunc`: Go's `Stop` checks `initTimer` (set by the runtime's
`newTimer`) and calls the runtime's `stopTimer`, which stops the timer if it has not fired (so
that `f` does not run) and reports whether it did; the model of `newTimer` runs `f` regardless,
so the result says nothing the proof can use. `isFuncTimer t` cannot be obtained for a timer
that is not `AfterFunc`'s (on which Go's `stopTimer` would treat the memory after the `Timer` as
runtime state): `initTimer` is unexported, and `wp_AfterFunc` withholds the points-to of `C`, so
the `Timer` cannot be copied.

(The two cases were two axioms, `Timer.wp_Stop` for `isTimer` and `Timer.wp_Stop_func` for
`isFuncTimer`; `Results.lean` derives them from this spec, as `Timer.wp_Stop_timer` and
`Timer.wp_Stop_func`.) -/
abbrev time.Timer.Stop.spec : Prop :=
  ∀ (t : Loc),
    {{ iprop((∃ (ch : Loc) (γ : ChanNames), isTimer (GF := GF) t ch γ) ∨ isFuncTimer (GF := GF) t) }}
      (App (Val (t @!! go.GoType.PointerType time.Timer.ty @!! go!"Stop")) (Val #()))
    {{ (b : Bool), RET #b; True }}

end spec

end Perennial
