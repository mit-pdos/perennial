/-
`slices.AppendSeq`'s spec.
-/
module

public import Perennial.Proof.slices.Base
public import Perennial.Golang.Theory.RangeFunc

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

/-- `slices.AppendSeq(s, seq)` (`for v := range seq { s = append(s, v) }`), for any slice type `S`
of elements `Et`: runs the iterator `seq` once, with what it needs (`R`, given back), appending
every element it yields, the list `xs` (`ok xs`); `s` (owned, with its capacity) becomes `s'`.
When `seq` yields nothing, `s'` is `s` (Go: "the result preserves the nilness of s"). -/
abbrev slices.AppendSeq.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (vs : List E) (seq : GoFunc) (R : IProp GF) (ok : List E → Prop),
    {{ s ↦* vs ∗ ownSliceCap E s (DFrac.own 1) ∗ iter.SeqRuns seq R ok ∗ R }}
      (App (App (Val #(functions slices.AppendSeq [S, Et])) (Val #s)) (Val #seq))
    {{ (s' : GoSlice) (xs : List E), RET #s';
        s' ↦* (vs ++ xs) ∗ ownSliceCap E s' (DFrac.own 1) ∗ R ∗
        ⌜ok xs ∧ (xs = [] → s' = s)⌝ }}

end spec

end Perennial
