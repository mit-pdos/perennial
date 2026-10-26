/-
The proof of `testTypeAssertionInterface` (a goose semantics test, `interfaces_complex.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testTypeAssertionInterface

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testTypeAssertionInterface.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testTypeAssertionInterface.spec (GF := GF) (hG := hG) := by
  semantics_auto

end proof

end Perennial
