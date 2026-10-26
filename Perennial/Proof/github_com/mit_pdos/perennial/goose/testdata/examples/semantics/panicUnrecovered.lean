/-
The proof of `panicUnrecovered` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicUnrecovered

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicUnrecovered.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.panicUnrecovered.spec (GF := GF) (hG := hG) := fun Φ => by
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_with_defer as %defer defer
  wp_apply wp_panic
  iexact HΦ

end proof

end Perennial
