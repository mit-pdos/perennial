/-
The proof of `sort.StringSlice.Sort`.
-/
module

public import Perennial.Spec.sort.StringSlice__Sort
public import Perennial.Spec.sort.StringSlice__Len
public import Perennial.Spec.sort.StringSlice__Less
public import Perennial.Spec.sort.StringSlice__Swap
public import Perennial.Spec.sort.Sort
public import Perennial.Proof.slices.SortBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.StringSlice.Sort.wp_proof
    (wp_Sort : sort.«Sort».spec (GF := GF) (hG := hG))
    (wp_Len : sort.StringSlice.Len.spec (GF := GF) (hG := hG))
    (wp_Less : sort.StringSlice.Less.spec (GF := GF) (hG := hG))
    (wp_Swap : sort.StringSlice.Swap.spec (GF := GF) (hG := hG)) :
    sort.StringSlice.Sort.spec (GF := GF) (hG := hG) := by
  intro x xs
  wp_start as ⟨Hx, %Hlen⟩
  wp_auto
  ihave #Hsrt : sort.isSorter (E := GoString) ⟨sort.StringSlice.ty, #x⟩ (fun l => x ↦* l)
      go.GoStringLt $$ []
  · unfold sort.isSorter
    isplitr
    · iintro !> %l
      iapply (wp_Len x l (DFrac.own 1))
    isplitr
    · iintro !> %l %i %j %a %b %H
      obtain ⟨hi, hj, ha, hb⟩ := H
      iintro !> %Φ' Hl HΦ'
      wp_apply wp_Less x l (DFrac.own 1) i j a b hi hj ha hb $$ Hl as Hl
      iapply HΦ'
      iframe
      ipureintro
      simp
    · iintro !> %l %i %j %a %b %H
      obtain ⟨hi, hj, ha, hb⟩ := H
      iintro !> %Φ' Hl HΦ'
      wp_apply wp_Swap x l i j a b hi hj ha hb $$ Hl as Hl
      iapply HΦ' $$ Hl
  wp_apply wp_Sort (E := GoString) ⟨sort.StringSlice.ty, #x⟩ (fun l => x ↦* l) go.GoStringLt
      slices.StrictWeakOrder_goStringLt xs $$ [Hx] as %xs' ⟨Hx, %Hperm, %Hsorted⟩
  · iframe Hx; iframe #; ipureintro; exact Hlen
  iapply HΦ
  iframe Hx
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
