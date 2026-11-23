/-
`time.Duration.Abs`'s spec.
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

/-- `d.Abs()`: `d` if it is not negative, the largest `Duration` for the smallest (whose negation
would overflow), `-d` otherwise. -/
abbrev time.Duration.Abs.spec : Prop :=
  ∀ (d : time.Duration),
    {{ (True : IProp GF) }}
      (App (Val (d @!! time.Duration.ty @!! go!"Abs")) (Val #()))
    {{ RET #(if 0 ≤ sint.Z d then d else if d = W64 (-9223372036854775808) then W64 9223372036854775807 else -d); True }}

end spec

end Perennial
