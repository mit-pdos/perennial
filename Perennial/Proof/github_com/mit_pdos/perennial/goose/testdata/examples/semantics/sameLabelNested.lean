/-
The proof of `sameLabelNested` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.sameLabelNested

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.sameLabelNested.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.sameLabelNested.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "%Hi" ∷ ⌜uint.Z i ≤ 3 ∧ uint.Z n = 3 * uint.Z i + 100 * (if uint.Z i ≤ 1 then uint.Z i else uint.Z i - 1)⌝ : IProp GF) $$ [i n]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by decide, by decide⟩
  wp_for HI
  wp_if_destruct
  · ihave HJ : (∃ j m : w64,
        "j" ∷ j_ptr ↦ j ∗
        "m" ∷ m_ptr ↦ m ∗
        "%Hj" ∷ ⌜uint.Z j ≤ 4 ∧ uint.Z m = (if uint.Z j ≤ 2 then uint.Z j else uint.Z j - 1)⌝ : IProp GF) $$ [j m]
    · iexists _, _
      iframe
      ipureintro; exact ⟨by decide, by decide⟩
    wp_for HJ
    wp_if_destruct
    · wp_for
      wp_if_destruct
      · -- `continue L` of the literal's loop
        wp_for_post
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro; constructor <;> word
      · wp_if_destruct
        · -- `break L` of the literal's loop: f returns m = 3
          wp_for_post
          wp_for_post
          have hm : m = W64 3 := by word
          subst hm
          wp_if_destruct
          · -- `continue L` of the outer loop at i = 1
            wp_for_post
            iframe
            iexists _, _
            iframe
            ipureintro; constructor <;> word
          · wp_for_post
            iframe
            iexists _, _
            iframe
            ipureintro
            constructor
            · word
            · by_cases h : uint.Z i = 0
              · have : i = W64 0 := by word
                subst this; word
              · have h2 : uint.Z i = 2 := by word
                have h3 : uint.Z (i + W64 1) = 3 := by word
                have hn : uint.Z n = 106 := by rw [Hi.2, h2]; decide
                rw [h3]; simp only [show ¬ ((3:Int) ≤ 1) by decide, if_false]; word
        · wp_for_post
          wp_for_post
          iframe
          iexists _, _
          iframe
          ipureintro; constructor <;> word
    · exfalso; word
  · have hi : uint.Z i = 3 := by word
    rw [show n = W64 209 by rw [hi] at Hi; word]
    iapply HΦ
    iexact Hpre

end proof

end Perennial
