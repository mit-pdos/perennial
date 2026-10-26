/-
`time.Time.addSec`'s spec.
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

/-- `(*Time).addSec(d)`: some new value of `*t`. -/
abbrev time.Time.addSec.spec : Prop :=
  ∀ (l : Loc) (tv : time.Time) (d : w64),
    {{ (l ↦ tv : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"addSec")) (Val #d))
    {{ (tv' : time.Time), RET #(); l ↦ tv' }}

end spec

end Perennial
