/-
`sort.Strings`'s spec.
-/
module

public import Perennial.Proof.sort.Base
public import Perennial.Golang.Theory.String

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

/-- `sort.Strings(x)` sorts `x` in place: it permutes the slice into ascending order (Go's order
on strings). The length bound is `slices.Sort`'s, which `Strings` calls. -/
abbrev sort.Strings.spec : Prop :=
  ∀ (x : GoSlice) (xs : List GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (@! Strings)) (Val #x))
    {{ (xs' : List GoString), RET #(); x ↦* xs' ∗
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜∀ (i j : Nat) (xi xj : GoString), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
          go.GoStringLe xi xj⌝ }}

end spec

end Perennial
