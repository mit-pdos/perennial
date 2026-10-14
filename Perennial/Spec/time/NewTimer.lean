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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `time.NewTimer(d)` (axiom): a `*Timer` (`isTimer`), one of the runtime's timers
(`newTimerMade`). -/
abbrev time.NewTimer.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (@! time.NewTimer)) (Val #d))
    {{ (t : Loc) (ch : Loc) (γ : ChanNames), RET #t; isTimer t ch γ }}

end spec

end Perennial
