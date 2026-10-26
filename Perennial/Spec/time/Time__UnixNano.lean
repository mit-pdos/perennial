/-
`time.Time.UnixNano`'s spec.
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

/-- `Time.UnixNano()`: some `int64`. -/
abbrev time.Time.UnixNano.spec : Prop :=
  ∀ (t : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"UnixNano")) (Val #()))
    {{ (x : w64), RET #x; True }}

end spec

end Perennial
