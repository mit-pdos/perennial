/-
The proof of `testLoopVarCapture` (a goose semantics test, `loopvars.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testLoopVarCapture

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testLoopVarCapture.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testLoopVarCapture.spec (GF := GF) (hG := hG) := by
  semantics_auto
  ihave HI : (∃ (p : Loc) (j : w64) (fv : GoFunc),
      "Hcell" ∷ «$iter_i_ptr» ↦ p ∗
      "Hp" ∷ p ↦ j ∗
      "f" ∷ f_ptr ↦ fv ∗
      "HΦ" ∷ Φ #true ∗
      "%Hj" ∷ ⌜uint.Z j ≤ 3⌝ ∗
      "Hf" ∷ (⌜uint.Z j ≤ 1 ∧ fv = zero_val GoFunc⌝ ∨
        ∃ q : Loc, q ↦ W64 1 ∗
          ⌜1 < uint.Z j ∧ fv = func.mk BAnon BAnon gl(exceptionDo (return: ![go.uint64] #q))⌝)
      : IProp GF) $$ [«$iter_i» i f HΦ]
  · iexists _, _, _
    iframe
    isplitr
    · ipureintro; decide
    · ileft; ipureintro; exact ⟨by decide, rfl⟩
  wp_for HI
  wp_if_destruct
  · wp_if_destruct
    · -- iteration 1 stores a closure over its own variable `p`
      wp_for_post
      iexists _, _, _
      iframe
      isplitr
      · ipureintro; decide
      · iright
        iexists p
        iframe
        ipureintro; exact ⟨by decide, rfl⟩
    · wp_for_post
      iexists _, _, _
      iframe
      isplitr
      · ipureintro; word
      · icases Hf with (%Hf | ⟨%q, Hq, %Hf⟩)
        · ileft; ipureintro
          have : j = W64 0 := by word
          subst this
          exact ⟨by decide, Hf.2⟩
        · iright
          iexists q
          iframe
          ipureintro; exact ⟨by word, Hf.2⟩
  · icases Hf with (%Hf | ⟨%q, Hq, %Hf⟩)
    · exfalso; word
    · rw [Hf.2]
      steps
      iexact HΦ

end proof

end Perennial
