/-
The proof of `recoverInLoop` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverInLoop

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverInLoop.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverInLoop.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_with_defer_recover as %defer %pnc defer pnc
  ihave HI : (∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "%Hn" ∷ ⌜uint.Z n ≤ 3⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · -- `i == 3`: the panic ends the loop
    wp_apply wp_panic
    wp_for_post
    wp_apply wp_recoverPanic $$ [$pnc] as pnc
    iapply HΦ
    itrivial
  · wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; word

end proof

end Perennial
