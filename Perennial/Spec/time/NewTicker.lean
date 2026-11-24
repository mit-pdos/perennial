/-
`time.NewTicker`'s spec.
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

/-- Spec of `time.NewTicker(d)`: for a positive `d` (Go panics otherwise), a `*Ticker`
(`isTicker`), one of the runtime's timers (`isRuntimeTimer`), whose channel may yield some time at
a receive. The ticker's goroutine sends `Now()` (`sendTimes`), which reads the package's globals,
hence `isPkgInit`. -/
abbrev time.NewTicker.spec : Prop :=
  ∀ (d : time.Duration),
    {{ isPkgInit (PROP := IProp GF) pkg_id.time ∗ ⌜0 < sint.Z d⌝ }}
      (App (Val (@! time.NewTicker)) (Val #d))
    {{ (t : Loc) (ch : Loc) (γ : ChanNames), RET #t; isTicker (GF := GF) t ch γ }}

end spec

end Perennial
