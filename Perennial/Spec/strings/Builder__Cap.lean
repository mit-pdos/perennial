/-
`strings.Builder.Cap`'s spec.
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

/-- `b.Cap()`: the buffer's capacity, some number at least the length of the accumulated string. -/
abbrev strings.Builder.Cap.spec : Prop :=
  ∀ (l : Loc) (s : GoString),
    {{ strings.ownBuilder (GF := GF) l s }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"Cap")) (Val #()))
    {{ (c : w64), RET #c; ⌜s.length ≤ sint.Z c⌝ ∗ strings.ownBuilder l s }}

end spec

end Perennial
