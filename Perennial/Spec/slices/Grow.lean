/-
`slices.Grow`'s spec.
-/
module

public import Perennial.Proof.slices.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- `slices.Grow(s, n)` (Go: panics if `n < 0`; else, if `s`'s spare capacity is less than `n`,
`s = append(s[:cap(s)], make([]E, n')...)[:len(s)]` for the missing `n'`): a slice `s'` with
`s`'s elements and at least `n` elements of spare capacity, owned. It may be `s` itself
(when the capacity already suffices, so `Grow(nil, 0)` is `nil`) or a fresh slice; `s`'s ownership passes to `s'`. -/
abbrev slices.Grow.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (xs : List V) (n : w64),
    {{ (s ↦* xs ∗ ownSliceCap V s (DFrac.own 1) ∗ ⌜0 ≤ sint.Z n⌝ : IProp GF) }}
      (App (App (Val #(functions slices.Grow [S, Et])) (Val #s)) (Val #n))
    {{ (s' : GoSlice), RET #s';
        s' ↦* xs ∗ ownSliceCap V s' (DFrac.own 1) ∗
        ⌜sint.Z n ≤ sint.Z s'.cap - sint.Z s'.len⌝ ∗
        ⌜sint.Z n ≤ sint.Z s.cap - sint.Z s.len → s' = s⌝ }}

end spec

end Perennial
