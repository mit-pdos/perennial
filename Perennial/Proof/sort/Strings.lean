/-
The proof of `sort.Strings`: `slices.Sort` at `[]string`, whose comparison `cmp.Less` at `string`
is Go's order on strings.
-/
module

public import Perennial.Spec.sort.Strings
public import Perennial.Spec.slices.Sort
public import Perennial.Spec.cmp.Less
public import Perennial.Proof.slices.OrderedBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

open Iris.ProofMode in
theorem sort.Strings.wp_proof
    (wp_Sort : slices.Sort.spec (GF := GF) (hG := hG))
    (wp_Less : cmp.Less.spec (GF := GF) (hG := hG)) :
    sort.Strings.spec (GF := GF) (hG := hG) := fun x xs => by
  wp_start as ⟨Hxs, %Hlen⟩
  wp_auto
  ihave #Hless := slices.lessImplements_string_of (GF := GF) wp_Less
  wp_apply wp_Sort go.GoStringLt x xs slices.StrictWeakOrder_goStringLt $$ [Hxs]
    with %xs' ⟨Hxs, %Hperm, %Hsorted⟩
  · iframe Hxs; iframe #; ipureintro; exact Hlen
  iapply HΦ
  iframe Hxs
  isplitl []
  · ipureintro; exact Hperm
  ipureintro
  intro i j xi xj Hi Hj Hij
  have hn := Hsorted i j xi xj Hi Hj Hij
  by_cases hlt : go.GoStringLt xi xj
  · exact Or.inr hlt
  · exact Or.inl (go.goStringLt_eq_of_not_lt hlt hn)

end proof

end Perennial
