/-
`slices.Collect`'s spec.
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

/-- `slices.Collect(seq)` (`AppendSeq([]E(nil), seq)`): runs the iterator `seq` once, with what it
needs (`R`, given back), and returns a fresh slice of the elements it yields, the list `xs`
(`ok xs`), whose whole capacity the caller owns; `nil` when `seq` yields nothing. -/
abbrev slices.Collect.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (seq : GoFunc) (R : IProp GF) (ok : List E → Prop),
    {{ iter.SeqRuns seq R ok ∗ R }}
      (App (Val #(functions slices.Collect [Et])) (Val #seq))
    {{ (s : GoSlice) (xs : List E), RET #s;
        s ↦* xs ∗ ownSliceCap E s (DFrac.own 1) ∗ R ∗ ⌜ok xs ∧ (xs = [] → s = slice.nil)⌝ }}

end spec

end Perennial
