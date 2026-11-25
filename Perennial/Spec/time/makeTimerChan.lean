/-
`time.makeTimerChan`'s spec.
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

/-- `makeTimerChan()`: a new channel of times (unbuffered or of capacity 1), with an update that
makes it a bag of times carrying any `Ψ` the caller chooses (`isChanBag`; used once). -/
abbrev time.makeTimerChan.spec : Prop :=
    {{ (True : IProp GF) }}
      (App (Val (@! time.makeTimerChan)) (Val #()))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        ∀ Ψ : time.Time → IProp GF, |={⊤}=> isChanBag γ ch (V := time.Time) Ψ }}

end spec

end Perennial
