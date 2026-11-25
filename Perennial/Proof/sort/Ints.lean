/-
The proof of `sort.Ints`: `slices.Sort` at `[]int`, whose comparison `cmp.Less` at `int` is `<` on
the signed values.
-/
module

public import Perennial.Spec.sort.Ints
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
theorem sort.Ints.wp_proof
    (wp_Sort : slices.Sort.spec (GF := GF) (hG := hG))
    (wp_Less : cmp.Less.spec (GF := GF) (hG := hG)) :
    sort.Ints.spec (GF := GF) (hG := hG) := fun x xs => by
  wp_start as ⟨Hxs, %Hlen⟩
  wp_auto
  ihave #Hless := slices.lessImplements_int_of (GF := GF) wp_Less
  wp_apply wp_Sort (fun (a b : w64) => sint.Z a < sint.Z b) x xs slices.StrictWeakOrder_signed_lt
      $$ [Hxs] with %xs' ⟨Hxs, %Hperm, %Hsorted⟩
  · iframe Hxs; iframe #; ipureintro; exact Hlen
  iapply HΦ
  iframe Hxs
  isplitl []
  · ipureintro; exact Hperm
  ipureintro
  intro i j xi xj Hi Hj Hij
  have hn := Hsorted i j xi xj Hi Hj Hij
  omega

end proof

end Perennial
