/-
`time.Time.After`'s spec.
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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : time.Assumptions]

/-- Spec of `Time.After`: whether `t` is after `u` (`time.Time.after`, which is `u.before t`). -/
abbrev time.Time.After.spec : Prop :=
  ∀ (t u : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"After")) (Val #u))
    {{ RET #(time.Time.after t u); True }}

end spec

end Perennial
