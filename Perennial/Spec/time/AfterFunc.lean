/-
`time.AfterFunc`'s spec.
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

/-- `AfterFunc(d, f)`: `f()` runs in a new goroutine (the model ignores the delay, and an
execution in which `f` never runs is a prefix of one in which it does), so it must be safe to
run then and must not panic. -/
abbrev time.AfterFunc.spec : Prop :=
  ∀ (d : time.Duration) (f : GoFunc),
    {{ (WP (App (Val #f) (Val #())) {{ (fun v : val => iprop(⌜v.isPanic = false⌝)) }} : IProp GF) }}
      (App (App (Val (@! time.AfterFunc)) (Val #d)) (Val #f))
    {{ (t : Loc), RET #t; isFuncTimer (GF := GF) t }}

end spec

end Perennial
