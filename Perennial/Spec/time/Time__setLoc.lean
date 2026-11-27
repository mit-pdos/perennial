/-
`time.Time.setLoc`'s spec.
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

/-- `(*Time).setLoc(loc)`: some new value of `*t` (its monotonic reading stripped and its location
set; `&utcLoc` is stored as nil). -/
abbrev time.Time.setLoc.spec : Prop :=
  ∀ (l : Loc) (tv : time.Time) (loc : Loc),
    {{ (l ↦ tv : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType time.Time.ty @!! go!"setLoc")) (Val #loc))
    {{ (tv' : time.Time), RET #(); l ↦ tv' }}

end spec

end Perennial
