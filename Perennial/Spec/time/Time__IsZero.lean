/-
`time.Time.IsZero`'s spec.
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

/-- `t.IsZero()`: whether `t` is the zero `Time` (Go tests `t.wall == 0 && t.ext == 0`, which is
`t.sec() == 0 && t.nsec() == 0`). -/
abbrev time.Time.IsZero.spec : Prop :=
  ∀ (t : time.Time),
    {{ (True : IProp GF) }}
      (App (Val (t @!! time.Time.ty @!! go!"IsZero")) (Val #()))
    {{ RET #(decide (t.wall' = W64 0 ∧ t.ext' = W64 0)); True }}

end spec

end Perennial
