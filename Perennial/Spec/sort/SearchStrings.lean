/-
`sort.SearchStrings`'s spec.
-/
module

public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.SearchStrings(a, x)` on an `a` sorted ascending (Go's order on strings): the index
where `x` would be inserted, between `0` and `len(a)`, every string before it less than `x` and
every string from it on at least `x`. -/
abbrev sort.SearchStrings.spec : Prop :=
  ∀ (a : GoSlice) (x : GoString) (q : DFrac) (xs : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ a ↦*{q} xs ∗
        ⌜ListSorted go.GoStringLe xs⌝ }}
      (App (App (Val (@! SearchStrings)) (Val #a)) (Val #x))
    {{ (i : w64), RET #i; a ↦*{q} xs ∗
        ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ xs.length⌝ ∗
        ⌜(∀ (j : Nat) x0, (j : Int) < sint.Z i → xs[j]? = some x0 → go.GoStringLt x0 x) ∧
         (∀ (j : Nat) x0, sint.Z i ≤ (j : Int) → xs[j]? = some x0 → go.GoStringLe x x0)⌝ }}

end spec

end Perennial
