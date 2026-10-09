/-
Proofs of the loop-variable tests of the goose `semantics` test package: each
iteration of a loop has its own iteration variables.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

/-- The closure stored in iteration 1 reads iteration 1's own variable, which
keeps the value 1 (the loop increments the next iteration's copy). -/
theorem wp_testLoopVarCapture : TestFunOk (GF := GF) testLoopVarCapture := by
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

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
