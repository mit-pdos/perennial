/-
`slices.choosePivotCmpFunc`'s spec.
-/
module

public import Perennial.Proof.slices.PartitionBasics

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

abbrev slices.choosePivotCmpFunc.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
    (a b : w64) (cmp_code : GoFunc) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ }}
      (App (App (App (App (Val #(functions choosePivotCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #cmp_code))
    {{ (r : w64) (hint : slices.sortedHint), RET (PairV #r #hint);
        data ↦* xs ∗
        "%Hr_bound" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ }}

end spec

end Perennial
