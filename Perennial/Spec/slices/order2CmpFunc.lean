/-
`slices.order2CmpFunc`'s spec.
-/
module

public import Perennial.Proof.slices.SortBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

abbrev slices.order2CmpFunc.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
    (a b : w64) (swaps_l : Loc) (cmp_code : GoFunc) (dq : DFrac) (xs : List E) (swaps : w64)
    (xa xb : E) (Ha_bound : 0 ≤ sint.Z a) (Hb_bound : 0 ≤ sint.Z b),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hxa" ∷ ⌜xs[sint.nat a]? = some xa⌝ ∗
        "%Hxb" ∷ ⌜xs[sint.nat b]? = some xb⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hcmp" ∷ cmpImplements R cmp_code }}
      (App (App (App (App (App (Val #(functions order2CmpFunc [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #swaps_l)) (Val #cmp_code))
    {{ (a' b' : w64) (swaps' : w64), RET (PairV #a' #b');
        data ↦*{dq} xs ∗
        ⌜(a' = a ∧ b' = b ∧ ¬ R xb xa) ∨ (a' = b ∧ b' = a ∧ R xb xa)⌝ ∗
        swaps_l ↦ swaps' }}

end spec

end Perennial
