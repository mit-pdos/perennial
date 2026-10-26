/-
`time.Time.Add`'s spec.
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

/-- Spec of `Time.Add`: some time. -/
abbrev time.Time.Add.spec : Prop :=
  ∀ (t : time.Time) (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"Add")) (Val #d))
    {{ (t : time.Time), RET #t; True }}

end spec

end Perennial
