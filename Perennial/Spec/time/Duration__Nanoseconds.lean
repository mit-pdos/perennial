/-
`time.Duration.Nanoseconds`'s spec.
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

/-- `d.Nanoseconds()`: `int64(d)`. -/
abbrev time.Duration.Nanoseconds.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (d @!! time.Duration.ty @!! go!"Nanoseconds")) (Val #()))
    {{ RET #d; True }}

end spec

end Perennial
