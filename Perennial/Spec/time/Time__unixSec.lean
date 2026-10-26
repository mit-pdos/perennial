/-
`time.Time.unixSec`'s spec.
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

/-- `(*Time).unixSec()`: some `int64`; `*t` unchanged. -/
abbrev time.Time.unixSec.spec : Prop :=
  ∀ (t : Loc) (tv : time.Time),
    {{ (t ↦ tv : IProp GF) }}
      (App (Val (t @!! go.GoType.PointerType time.Time.ty @!! go!"unixSec")) (Val #()))
    {{ (x : w64), RET #x; t ↦ tv }}

end spec

end Perennial
