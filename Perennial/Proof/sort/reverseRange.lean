/-
The proof of `sort.reverseRange` over a `sort.Interface`: the proof of `slices.reverseRangeCmpFunc`
(`Perennial/Proof/slices/reverseRangeCmpFunc.lean`) with `Less`/`Swap` calls.
-/
module

public import Perennial.Spec.sort.reverseRange
public import Perennial.Proof.sort.SorterBasics

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open slices

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.reverseRange.wp_proof : sort.reverseRange.spec (GF := GF) (hG := hG) := fun {E} x own R _ a b xs => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as H
  iNamed H
  wp_auto
  ihave HI : (∃ (xs1 : List E) (i_val j_val : w64),
      "Hxs" ∷ own xs1 ∗
      "i" ∷ i_ptr ↦ i_val ∗
      "j" ∷ j_ptr ↦ j_val ∗
      "%ij_bound" ∷ ⌜sint.Z a ≤ sint.Z i_val ∧ sint.Z j_val < sint.Z b⌝ ∗
      "%HPerm1" ∷ ⌜xs ≡ₚ xs1⌝ ∗
      "%Houtside1" ∷ ⌜OutsideSame xs xs1 (sint.nat a) (sint.nat b)⌝ : IProp GF) $$ [Hxs i j]
  · iexists xs, _, _
    iframe
    ipureintro
    exact ⟨by word, List.Perm.refl _, outsideSame_refl _ _ _⟩
  wp_for HI
  wp_if_destruct
  · have Hl := HPerm1.length_eq
    list_elem xs1 (sint.nat j_val) as xj
    list_elem xs1 (sint.nat i_val) as xi
    wp_apply wp_sorter_Swap x own R xs1 i_val j_val xi xj (by word) (by word)
      Hxi_lookup Hxj_lookup $$ [$Hsrt $Hxs] as Hxs
    wp_for_post
    iframe
    iexists _, _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, ?_⟩
    · exact HPerm1.trans (swap_perm xs1 (sint.nat i_val) (sint.nat j_val) xi xj
        Hxi_lookup Hxj_lookup)
    · exact outsideSame_trans _ _ _ _ _ Houtside1
        (outsideSame_swap _ _ _ _ _ _ _ ⟨by word, by word⟩ ⟨by word, by word⟩)
  · iapply HΦ
    iframe
    ipureintro
    exact ⟨HPerm1, Houtside1⟩

end proof

end Perennial
