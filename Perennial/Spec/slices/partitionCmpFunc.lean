/-
`slices.partitionCmpFunc`'s spec.
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

abbrev slices.partitionCmpFunc.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
    (a b pivot : w64) (cmp_code : GoFunc) (xs : List E),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦* xs ∗
        "%Hab_bound" ∷ ⌜0 ≤ sint.Z a ∧ sint.Z a < sint.Z b ∧ sint.Z b ≤ xs.length ∧
          xs.length ≤ 2 ^ 62⌝ ∗
        "#Hcmp" ∷ cmpImplements R cmp_code ∗
        "%pivot_range" ∷ ⌜sint.Z a ≤ sint.Z pivot ∧ sint.Z pivot < sint.Z b⌝ }}
      (App (App (App (App (App (Val #(functions partitionCmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #pivot)) (Val #cmp_code))
    {{ (xs' : List E) (bl : Bool) (r : w64), RET (PairV #r #bl);
        data ↦* xs' ∗
        "%range" ∷ ⌜sint.Z a ≤ sint.Z r ∧ sint.Z r < sint.Z b⌝ ∗
        "%Hperm" ∷ ⌜xs ≡ₚ xs'⌝ ∗
        "%Hpart" ∷ ⌜IsPartitioned R xs' (sint.nat a) (sint.nat b) (sint.nat r)⌝ ∗
        "%Houtside" ∷ ⌜OutsideSame xs xs' (sint.nat a) (sint.nat b)⌝ }}

end spec

end Perennial
