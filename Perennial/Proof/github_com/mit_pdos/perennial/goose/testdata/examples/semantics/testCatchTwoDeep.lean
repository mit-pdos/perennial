/-
The proof of `testCatchTwoDeep` (a goose semantics test, `recover.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCatchTwoDeep
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCatchTwoDeep.wp_proof
    (wp_catchTwoDeep : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCatchTwoDeep.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_apply wp_catchTwoDeep
  iexact HΦ

end proof

end Perennial
