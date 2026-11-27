/-
`slices.Repeat`'s spec.
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

/-- `slices.Repeat(x, count)` (Go: panics with "cannot be negative" on a negative `count`, and
with "the result of (len(x) * count) overflows" when `len(x) * count` (`bits.Mul`) exceeds the
largest `int`; otherwise `make(S, len(x)*count)`, filled by copying `x` and then doubling the copied
prefix), for any slice type `S` of elements `Et`: a fresh slice `s'` holding `count` copies of `x`'s
elements in turn, whose whole capacity it owns; `x` is only read.

The premises are the two panics' conditions: `count` is not negative, and the length of the result
is below `2^63`. -/
abbrev slices.Repeat.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (x : GoSlice) (dq : DFrac) (xs : List V) (count : w64),
    0 ≤ sint.Z count → xs.length * sint.Z count < 2 ^ 63 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗ x ↦*{dq} xs }}
      (App (App (Val #(functions slices.Repeat [S, Et])) (Val #x)) (Val #count))
    {{ (s' : GoSlice), RET #s';
        x ↦*{dq} xs ∗ s' ↦* (List.replicate (sint.nat count) xs).flatten ∗
        ownSliceCap V s' (DFrac.own 1) }}

end spec

end Perennial
