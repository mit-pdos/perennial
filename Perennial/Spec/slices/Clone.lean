/-
`slices.Clone`'s spec.
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

/-- `slices.Clone(s)` (Go: `if s == nil { return nil }; return append(S{}, s...)`), for any
slice type `S` of elements `Et`: a fresh slice `s'` holding `s`'s elements (a shallow copy),
whose whole capacity it owns, so it does not alias `s`; `s` is only read. It preserves nilness:
`s'` is `nil` exactly when `s` is (an empty non-nil `s` gives an empty non-nil `s'`). -/
abbrev slices.Clone.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (dq : DFrac) (xs : List V),
    {{ (s ↦*{dq} xs : IProp GF) }}
      (App (Val #(functions slices.Clone [S, Et])) (Val #s))
    {{ (s' : GoSlice), RET #s';
        s ↦*{dq} xs ∗ s' ↦* xs ∗ ownSliceCap V s' (DFrac.own 1) ∗
        ⌜s' = slice.nil ↔ s = slice.nil⌝ }}

end spec

end Perennial
