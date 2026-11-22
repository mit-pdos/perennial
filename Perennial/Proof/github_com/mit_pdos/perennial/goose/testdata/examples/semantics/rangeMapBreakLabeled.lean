/-
The proof of `rangeMapBreakLabeled` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapBreakLabeled

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapBreakLabeled.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapBreakLabeled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply (wp_map_for_range (fun keys i => iprop(
      "n" ∷ n_ptr ↦ W64 0 ∗ "HΦ" ∷ (True -∗ Φ #(W64 1)) ∗ "«$res0»" ∷ «$res0_ptr» ↦ W64 0 ∗
      "%Hi" ∷ ⌜i = 0 ∧ keys ≠ []⌝))) $$ Hm
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  have hne : keys ≠ [] := by
    intro h
    have := (Hmem (W64 3)).2 (by simp)
    simp [h] at this
  isplitl [n HΦ «$res0»]
  · iframe
    ipureintro; exact ⟨rfl, hne⟩
  isplitr
  · imodintro
    iintro %i %key %v %_ ⟨n, HΦ, «$res0», %Hi⟩
    wp_auto
    ihave HJ : (True : IProp GF) $$ []
    · itrivial
    wp_for HJ
    wp_for_post
    unfold forMapPostcondition
    iright; iright; ileft
    isplitr
    · ipureintro; rfl
    iintro Hm
    wp_auto
    iapply exact_eq ?_ $$ (HΦ $$ [])
    · rfl
    · itrivial
  · iintro ⟨n, HΦ, «$res0», %Hi⟩ Hm
    exfalso
    apply Hi.2
    apply List.eq_nil_of_length_eq_zero
    omega

end proof

end Perennial
