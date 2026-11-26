/-
`time.Time.Equal`'s spec.
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

/-- Spec of `Time.Equal`: whether `t` and `u` are the same instant (`time.Time.equal`: their
monotonic readings when both have one, else their wall clocks' `(sec, nsec)`). -/
abbrev time.Time.Equal.spec : Prop :=
  ∀ (t u : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Equal")) (Val #u))
    {{ RET #(time.Time.equal t u); True }}

end spec

end Perennial
