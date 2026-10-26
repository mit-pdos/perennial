/-
`slices.medianOrdered`'s spec.
-/
module

public import Perennial.Proof.slices.OrderedPartitionBasics

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

abbrev slices.medianOrdered.spec : Prop :=
  ∀ {E : Type} [ZeroVal E] [TypedPointsto (GF := GF) E] {Et : go.GoType}
    [IntoValTyped (GF := GF) E Et] (R : E → E → Prop) [StrictWeakOrder R] (data : GoSlice)
    (a b c : w64) (swaps_l : Loc) (dq : DFrac) (xs : List E) (swaps : w64),
    {{ isPkgInit (PROP := IProp GF) pkg_id.slices ∗
        "Hxs" ∷ data ↦*{dq} xs ∗
        "%Hbounds" ∷ ⌜(0 ≤ sint.Z a ∧ sint.Z a < (xs.length : Int)) ∧
                      (0 ≤ sint.Z b ∧ sint.Z b < (xs.length : Int)) ∧
                      (0 ≤ sint.Z c ∧ sint.Z c < (xs.length : Int))⌝ ∗
        "Hswaps" ∷ swaps_l ↦ swaps ∗
        "#Hless" ∷ lessImplements (Et := Et) R }}
      (App (App (App (App (App (Val #(functions medianOrdered [Et])) (Val #data)) (Val #a))
        (Val #b)) (Val #c)) (Val #swaps_l))
    {{ (r : w64) (swaps' : w64), RET #r;
        data ↦*{dq} xs ∗
        ⌜r = a ∨ r = b ∨ r = c⌝ ∗
        swaps_l ↦ swaps' }}

end spec

end Perennial
