/-
`time.After`'s spec.
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

/-- `time.After(d)`: a channel on which a receive may yield some time (a bag of times,
`isChanBag`, with no logical content). -/
abbrev time.After.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (@! time.After)) (Val #d))
    {{ (ch : Loc) (γ : ChanNames), RET #ch;
        isChanBag γ ch (V := time.Time) (fun _ => iprop(True)) }}

end spec

end Perennial
