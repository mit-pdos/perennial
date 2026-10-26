/-
The proof of `sort.Reverse`.
-/
module

public import Perennial.Spec.sort.Reverse
public import Perennial.Proof.sort.SorterBasics

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

theorem sort.Reverse.wp_proof : sort.Reverse.spec (GF := GF) (hG := hG) := fun {E} x own R => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as #Hsrt
  wp_auto
  wp_alloc l as Hl
  ipersist Hl
  ihave Hl2 := Hl
  iStructNamed Hl2
  wp_auto
  iapply HΦ
  iapply isSorter_intro
  isplitr
  · iintro !> %l' %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Len x own R l' $$ [$Hsrt $Hown] as Hown
    iapply HΦ' $$ Hown
  isplitr
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    rw [method_unfold (t := reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Less x own R l' j i b a Hij.2.1 Hij.1 Hij.2.2.2 Hij.2.2.1
      $$ [$Hsrt $Hown] as %r ⟨Hown, %Hr⟩
    iapply HΦ'
    iframe Hown
    ipureintro; exact Hr
  · iintro !> %l' %i %j %a %b %Hij %Φ' !> Hown HΦ'
    dsimp only
    rw [method_unfold (t := go.GoType.PointerType reverse.ty)]
    wp_auto
    wp_apply wp_sorter_Swap x own R l' i j a b Hij.1 Hij.2.1 Hij.2.2.1 Hij.2.2.2
      $$ [$Hsrt $Hown] as Hown
    iapply HΦ'
    rw [swap_set_comm l' (sint.nat i) (sint.nat j) a b Hij.2.2.1 Hij.2.2.2]
    iexact Hown

end proof

end Perennial
