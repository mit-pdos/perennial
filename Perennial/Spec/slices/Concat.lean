/-
`slices.Concat`'s spec.
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
/-- `slices.Concat(slices...)` (Go: sums the lengths, panicking with "len out of range" if the
sum overflows `int`; then `Grow(nil, size)` and `append`s each slice in turn), for any slice type
`S` of elements `Et`: a fresh slice `s'` holding the elements of each slice in turn, whose whole
capacity it owns (it aliases none of the inputs), reading the slices only (at any fraction: the
same slice may appear several times). It is `nil` when the total is `0` (also for no slices).

The premise bounds the total length by `2^63`: Go panics otherwise, and the panic is reachable,
since the inputs may alias one another (`make([]T, 1<<32)` passed `1<<31` times takes a few
gigabytes and overflows the sum), as with `strings.Join` (README, "Model assumptions
(overflow)"). -/
abbrev slices.Concat.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (ss : GoSlice) (dq : DFrac) (sls : List GoSlice) (xss : List (List V)) (dq' : DFrac),
    sls.length = xss.length → (xss.map List.length).sum < 2 ^ 63 →
    {{ ss ↦*{dq} sls ∗ [∗list] p ∈ sls.zip xss, (p.1 ↦*{dq'} p.2 : IProp GF) }}
      (App (Val #(functions slices.Concat [S, Et])) (Val #ss))
    {{ (s' : GoSlice), RET #s';
        ss ↦*{dq} sls ∗ ([∗list] p ∈ sls.zip xss, p.1 ↦*{dq'} p.2) ∗
        s' ↦* xss.flatten ∗ ownSliceCap V s' (DFrac.own 1) ∗
        ⌜xss.flatten = [] → s' = slice.nil⌝ }}


end spec

end Perennial
