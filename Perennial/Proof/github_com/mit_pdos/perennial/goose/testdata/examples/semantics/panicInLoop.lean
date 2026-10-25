/-
The proof of `panicInLoop` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicInLoop

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicInLoop.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicInLoop.spec (GF := GF) (hG := hG) := fun Φ => by
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  ihave HI : (∃ n : w64, "i" ∷ i_ptr ↦ n ∗ "%Hn" ∷ ⌜uint.Z n ≤ 3⌝ : IProp GF) $$ [i]
  · iexists _; iframe; ipureintro; decide
  wp_for HI
  wp_if_destruct
  · -- `i == 3`: the panic ends the loop (`wp_for_post_panic`) and the function
    wp_apply wp_panic
    wp_for_post
    iexact HΦ
  · wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; word

end proof

end Perennial
