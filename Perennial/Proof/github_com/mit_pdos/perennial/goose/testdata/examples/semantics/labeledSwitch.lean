/-
The proof of `labeledSwitch` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledSwitch

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledSwitch.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledSwitch.spec (GF := GF) (hG := hG) := by
  intro x
  wp_start
  wp_auto
  wp_if_destruct
  · ihave HI : (∃ k n : w64,
        "k" ∷ k_ptr ↦ k ∗
        "n" ∷ n_ptr ↦ n ∗
        "%Hk" ∷ ⌜n = k ∧ uint.Z k ≤ 1⌝ : IProp GF) $$ [k n]
    · iexists _, _
      iframe
      ipureintro; exact ⟨rfl, by word⟩
    wp_for HI
    wp_if_destruct
    · wp_if_destruct
      · wp_for_post
        rw [Hif]
        iapply HΦ
        iexact Hpre
      · wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        constructor
        · rw [Hk.1]
        · word
    · exfalso; word
  · simp only [Hif, ↓reduceIte]
    iapply HΦ
    iexact Hpre

end proof

end Perennial
