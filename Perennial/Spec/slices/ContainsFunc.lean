/-
`slices.ContainsFunc`'s spec.
-/
module

public import Perennial.Spec.slices.IndexFunc

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

/-- `slices.ContainsFunc(s, f)` (Go: `return IndexFunc(s, f) >= 0`), for any slice type `S` of
elements `Et`: `f` is called on the elements in order until it answers `true`; the result is
`true` when an element answered `true`, `false` when every element answered `false`. `s` is
only read. For a pure predicate (`P x b := b = p x`) the result is `decide (∃ x ∈ xs, p x)`
(`slices.wp_ContainsFunc_pure`). -/
abbrev slices.ContainsFunc.spec : Prop :=
  ∀ {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] {Et : go.GoType}
    [IntoValTyped (GF := GF) V Et] {S : go.GoType} [S ↓u go.SliceType Et]
    (s : GoSlice) (dq : DFrac) (xs : List V) (f : GoFunc) (P : V → Bool → Prop),
    {{ s ↦*{dq} xs ∗ slices.funcAnswers (GF := GF) P xs f }}
      (App (App (Val #(functions slices.ContainsFunc [S, Et])) (Val #s)) (Val #f))
    {{ (b : Bool), RET #b;
        s ↦*{dq} xs ∗
        ⌜if b then ∃ x ∈ xs, P x true else ∀ x ∈ xs, P x false⌝ }}

end spec

end Perennial
