/-
The proof of `labeledBreak` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledBreak

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledBreak.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledBreak.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "%Hi" ∷ ⌜uint.Z i ≤ 2 ∧ uint.Z n = 10 * uint.Z i⌝ : IProp GF) $$ [i n]
  · iexists _, _
    iframe
    ipureintro; exact ⟨by decide, rfl⟩
  wp_for HI
  wp_if_destruct
  · ihave HJ : (∃ j n' : w64,
        "j" ∷ j_ptr ↦ j ∗
        "n" ∷ n_ptr ↦ n' ∗
        "%Hj" ∷ ⌜uint.Z j ≤ 10 ∧ uint.Z n' = 10 * uint.Z i + uint.Z j ∧
          (uint.Z i = 2 → uint.Z j ≤ 3)⌝ : IProp GF) $$ [j n]
    · iexists _, _
      iframe
      ipureintro; word
    wp_for HJ
    wp_if_destruct
    · wp_if_destruct
      · -- `break L`
        wp_for_post
        wp_for_post
        have : n' = W64 23 := by word
        subst this
        iapply HΦ
        iexact Hpre
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun h => ?_⟩
        have := Hj.2.2 h
        word
    · wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      have : uint.Z i ≠ 2 := fun h => by have := Hj.2.2 h; word
      word
  · exfalso; word

end proof

end Perennial
