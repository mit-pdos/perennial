/-
The proof of `rangeIntLabeled` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeIntLabeled

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeIntLabeled.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeIntLabeled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ r iv nv : w64,
      "«$range_i»" ∷ «$range_i_ptr» ↦ r ∗
      "i" ∷ i_ptr ↦ iv ∗
      "n" ∷ n_ptr ↦ nv ∗
      "%Hr" ∷ ⌜(sint.Z r = 0 ∧ uint.Z nv = 0) ∨ (sint.Z r = 1 ∧ uint.Z nv = 0) ∨
        (sint.Z r = 2 ∧ uint.Z nv = 1) ∨ (sint.Z r = 3 ∧ uint.Z nv = 3) ∨
        (sint.Z r = 4 ∧ uint.Z nv = 6)⌝ : IProp GF) $$ [«$range_i» i n]
  · iexists _, _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  wp_if_destruct
  · ihave HJ : (∃ j rj nv' : w64,
        "j" ∷ j_ptr ↦ j ∗
        "«$range_i»" ∷ «$range_i_ptr» ↦ rj ∗
        "n" ∷ n_ptr ↦ nv' ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z rj ∧ sint.Z rj ≤ sint.Z r ∧ uint.Z nv' = uint.Z nv + sint.Z rj ∧
          (sint.Z r = 4 → sint.Z rj = 0)⌝ :
        IProp GF) $$ [j «$range_i» n]
    · iexists _, _, _
      iframe
      ipureintro
      rw [show (zero_val w64) = W64 0 from rfl]
      word
    wp_for HJ
    wp_if_destruct
    · wp_if_destruct
      · -- `break L` at `i = 4`
        wp_for_post
        wp_for_post
        rw [show nv' = W64 6 by word]
        iapply HΦ
        iexact Hpre
      · wp_if_destruct
        · -- `continue L` at `j = i`
          wp_for_post
          wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro; word
        · wp_for_post
          iframe
          iexists _, _, _
          iframe
          ipureintro; word
    · exfalso; word
  · exfalso; word

end proof

end Perennial
