/-
The proof of `testFallthroughBreak` (a goose semantics test, `control_flow.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFallthroughBreak

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFallthroughBreak.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFallthroughBreak.spec (GF := GF) (hG := hG) := by
  semantics_auto
  ihave HI : (∃ i n : w64,
      "i" ∷ i_ptr ↦ i ∗
      "n" ∷ n_ptr ↦ n ∗
      "HΦ" ∷ Φ #true ∗
      "%Hi" ∷ ⌜(i = W64 0 ∧ n = W64 0) ∨ (i = W64 1 ∧ n = W64 101) ∨
        (i = W64 2 ∧ n = W64 211)⌝ : IProp GF) $$ [i n HΦ]
  · iexists _, _
    iframe
    ipureintro; left; exact ⟨rfl, rfl⟩
  wp_for HI
  rcases Hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> wp_if_destruct <;>
    try (exfalso; word)
  · wp_for_post
    iexists _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, rfl⟩
  · wp_for_post
    iexists _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, rfl⟩
  · iexact HΦ

end proof

end Perennial
