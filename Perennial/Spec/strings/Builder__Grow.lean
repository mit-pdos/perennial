/-
`strings.Builder.Grow`'s spec.
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

/-- `(*Builder).Grow(n)`, for `n ≥ 0`: the Builder at `l` keeps its string `s` (with room for `n`
more bytes, which the spec does not promise). The bound `s.length + n < 2^61` keeps `grow`'s new
capacity, `2*cap(b.buf) + n`, from overflowing: the model does not bound a slice's capacity by
its length (`append`'s and `MakeNoZero`'s capacities are arbitrary), and `cap(b.buf)` is below
`s.length + n` whenever `grow` runs. -/
abbrev strings.Builder.Grow.spec : Prop :=
  ∀ (l : Loc) (s : GoString) (n : w64),
    {{ strings.ownBuilder (GF := GF) l s ∗ ⌜0 ≤ sint.Z n ∧ s.length + sint.Z n < 2 ^ 61⌝ }}
      (App (Val (l @!! go.GoType.PointerType strings.Builder.ty @!! go!"Grow")) (Val #n))
    {{ RET #(); strings.ownBuilder l s }}

end spec

end Perennial
