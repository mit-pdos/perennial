/-
`sort.Ints`'s spec.
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

/-- `sort.Ints(x)` sorts `x` in place: it permutes the slice into ascending order of the signed
values. The length bound is `slices.Sort`'s, which `Ints` calls. -/
abbrev sort.Ints.spec : Prop :=
  ∀ (x : GoSlice) (xs : List w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ x ↦* xs ∗ ⌜xs.length ≤ 2 ^ 62⌝ }}
      (App (Val (@! Ints)) (Val #x))
    {{ (xs' : List w64), RET #(); x ↦* xs' ∗
        ⌜xs ≡ₚ xs'⌝ ∗
        ⌜∀ (i j : Nat) (xi xj : w64), xs'[i]? = some xi → xs'[j]? = some xj → i < j →
          sint.Z xi ≤ sint.Z xj⌝ }}

end spec

end Perennial
