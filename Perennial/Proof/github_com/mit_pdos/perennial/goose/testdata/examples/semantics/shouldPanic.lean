/-
The proof of `shouldPanic` (a goose semantics test, `panic.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.shouldPanic

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.shouldPanic.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.shouldPanic.spec (GF := GF) (hG := hG) := fun Φ => by
  iintro Hstuck
  wp_func_call
  wp_call
  wp_apply wp_panic
  iapply Hstuck

end proof

end Perennial
