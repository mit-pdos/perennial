/-
`strings.Builder.copyCheck`'s spec.
-/
module

public import Perennial.Proof.strings.BuilderBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `b.copyCheck()` on a `Builder` whose `addr` is `b` or nil: sets `addr` to `b`. (A copy by
value, whose `addr` is another address, panics in Go; the precondition excludes it.) -/
abbrev strings.Builder.copyCheck.spec : Prop :=
  ∀ (l : Loc) (b : strings.Builder),
    {{ (l ↦ b ∗ ⌜b.addr' = l ∨ b.addr' = null⌝ : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"copyCheck")) (Val #()))
    {{ RET #(); l ↦ ({ b with addr' := l } : strings.Builder) }}

end spec

end Perennial
