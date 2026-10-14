/-
The proof of `testBreakSwitch` (a goose semantics test, `control_flow.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testBreakSwitch

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testBreakSwitch.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testBreakSwitch.spec (GF := GF) (hG := hG) := by
  semantics_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "HΦ" ∷ Φ #true ∗
      "%Hi" ∷ ⌜n = i ∧ uint.Z i ≤ 3⌝ : IProp GF) $$ [i n HΦ]
  · iexists _, _
    iframe
    ipureintro; exact ⟨rfl, by decide⟩
  wp_for HI
  wp_if_destruct
  · repeat (first | wp_if_destruct | wp_auto)
    · wp_for_post
      iexists _, _
      iframe
      ipureintro; word
    · by_cases h2 : i = W64 2
      · subst h2
        wp_auto
        wp_for_post
        iexists _, _
        iframe
        ipureintro; word
      · simp only [h2, decide_false]
        wp_auto
        wp_for_post
        iexists _, _
        iframe
        ipureintro; word
  · iapply exact_eq ?_ $$ HΦ
    have : n = W64 3 := by word
    simp [this]

end proof

end Perennial
