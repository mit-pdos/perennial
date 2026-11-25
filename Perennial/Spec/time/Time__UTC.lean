/-
`time.Time.UTC`'s spec.
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

/-- `t.UTC()`: some `Time` (`t` with its location set to UTC, on the receiver's copy). It takes
only `&utcLoc`'s address, never reads a package variable, hence no `isPkgInit`. -/
abbrev time.Time.UTC.spec : Prop :=
  ∀ (t : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"UTC")) (Val #()))
    {{ (t' : time.Time), RET #t'; True }}

end spec

end Perennial
