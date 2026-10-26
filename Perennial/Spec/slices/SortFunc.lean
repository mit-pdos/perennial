/-
`slices.SortFunc`'s spec.
-/
module

public import Perennial.Proof.slices.PdqSortBasics
public import Perennial.Proof.slices.OrderedBasics

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

abbrev slices.SortFunc.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) {S : go.GoType} [S ↓u go.SliceType Et]
    (data : GoSlice) (cmp_code : GoFunc) (xs : List E) (SWO : StrictWeakOrder R),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hlength_bound" ∷ ⌜xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpImplements R cmp_code }}
      (App (App (Val #(functions SortFunc [S, Et])) (Val #data)) (Val #cmp_code))
    {{ (xs' : List E), RET #();
        "Hxs" ∷ data ↦* xs' ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hsorted" ∷ ⌜∀ (i j : Nat) (xi xj : E), xs'[i]? = some xi → xs'[j]? = some xj →
          i < j → ¬ R xj xi⌝ }}

end spec

end Perennial
