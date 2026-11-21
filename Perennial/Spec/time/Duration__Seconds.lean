/-
`time.Duration.Seconds`'s spec.
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

/-- `d.Seconds()`: some `float64` (`float64(d / Second) + float64(d % Second) / 1e9`, over the
semantics' uninterpreted floating-point operations). -/
abbrev time.Duration.Seconds.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (d @!! time.Duration.ty @!! go!"Seconds")) (Val #()))
    {{ (f : w64), RET #f; True }}

end spec

end Perennial
