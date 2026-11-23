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

/-- `b.copyCheck()` on a `Builder` whose `addr` is nil or `b` (`ownBuilderAddr`): `addr` is `b`.
(A copy by value, whose `addr` is another address, panics in Go; the precondition excludes it.) -/
abbrev strings.Builder.copyCheck.spec : Prop :=
  ∀ (l : Loc) (used : Bool),
    {{ (⌜l ≠ null⌝ ∗ strings.ownBuilderAddr l used : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"copyCheck")) (Val #()))
    {{ RET #(); strings.ownBuilderAddr l true }}

end spec

end Perennial
