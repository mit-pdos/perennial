/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.intSliceLoop`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.intSliceLoop

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.intSliceLoop.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.intSliceLoop.spec (GF := GF) (hG := hG) := fun s xs => by
  wp_start as Hs
  wp_auto
  ihave %Hs_len := ownSlice_len _ _ _ $$ Hs
  ihave %Hs_wf := ownSlice_wf _ _ _ $$ Hs
  ihave HI : (∃ i sum : w64,
      "i" ∷ i_ptr ↦ i ∗
      "xs" ∷ xs_ptr ↦ s ∗
      "sum" ∷ sum_ptr ↦ sum ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z s.len⌝ : IProp GF) $$ [i sum xs]
  · iexists _, _
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, Hif⟩)]
    obtain ⟨x_i, Hx_i⟩ : ∃ x, xs[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by simp only [sint.nat, sint.Z] at Hs_len Hi Hif ⊢; omega)⟩
    wp_apply wp_load_slice_index _ _ _ _ x_i Hi.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx_i
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro; word
  · iapply HΦ
    iframe

end proof

end Perennial
