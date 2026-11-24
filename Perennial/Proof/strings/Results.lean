/-
Results of `strings` derived from the linked ones: `Join` with its length premise discharged per
element and by count (`strings.wp_Join_bounded`).
-/
module

public import Perennial.Proof.strings.Link
public import Perennial.Proof.strings.JoinBounded

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section results
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

/-- `strings.Join` of `n` elements of at most `B` bytes each, `n * (B + |sep|) < joinMax`. -/
theorem strings.wp_Join_bounded :
    ∀ (elems : GoSlice) (xs : List GoString) (dq : DFrac) (sep : GoString) (B : Nat),
    (∀ x ∈ xs, x.length ≤ B) → xs.length * (B + sep.length) < strings.joinMax →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strings ∗ elems ↦*{dq} xs }}
      (App (App (Val (@! strings.Join)) (Val #elems)) (Val #sep))
    {{ RET #(sep.intercalate xs); elems ↦*{dq} xs }} :=
  strings.Join_bounded_of strings.wp_Join

end results

end Perennial
