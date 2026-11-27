/-
`time.NewTimer`'s spec.
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

/-- Spec of `time.NewTimer(d)`: a `*Timer` (`isTimer`), one of the runtime's timers
(`isRuntimeTimer`). The timer's goroutine sends `Now()` (`sendTimes`), which reads the package's
globals, hence `isPkgInit`. -/
abbrev time.NewTimer.spec : Prop :=
  ∀ (d : time.Duration),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time }}
      (App (Val (@! time.NewTimer)) (Val #d))
    {{ (t : Loc) (ch : Loc) (γ : ChanNames), RET #t; isTimer t ch γ }}

end spec

end Perennial
