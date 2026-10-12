/-
`sort.SearchInts`'s spec.
-/
module

public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- `sort.SearchInts(a, x)` on a sorted `a`: the index where `x` would be inserted, every
element before it less than `x` and every element from it on at least `x`. -/
abbrev sort.SearchInts.spec : Prop :=
  ∀ (a : GoSlice) (x : w64) (q : DFrac) (xs : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ a ↦*{q} xs ∗
        ⌜ListSorted (fun (i j : w64) => sint.Z i ≤ sint.Z j) xs⌝ }}
      (App (App (Val (@! SearchInts)) (Val #a)) (Val #x))
    {{ (i : w64), RET #i; a ↦*{q} xs ∗
        ⌜(∀ (j : Nat) x0, (j : Int) < sint.Z i → xs[j]? = some x0 → sint.Z x0 < sint.Z x) ∧
         (∀ (j : Nat) x0, sint.Z i ≤ (j : Int) → xs[j]? = some x0 → sint.Z x ≤ sint.Z x0)⌝ }}

end spec

end Perennial
