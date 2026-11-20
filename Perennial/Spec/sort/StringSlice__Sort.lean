/-
`sort.StringSlice.Sort`'s spec.
-/
module

public import Perennial.Proof.sort.Base

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

/-- `x.Sort()` for `x` a `StringSlice`: `sort.Sort(x)`, so the slice holds a permutation of its
strings in ascending order (Go's byte-wise order); as `sort.Sort`, for at most `2^62` elements. -/
abbrev sort.StringSlice.Sort.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (x @!! sort.StringSlice.ty @!! go!"Sort")) (Val #()))
    {{ (xs' : List GoString), RET #(); x ↦* xs' ∗ ⌜xs ≡ₚ xs'⌝ ∗
        ⌜∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
          go.GoStringLe xi xj⌝ }}

end spec

end Perennial
