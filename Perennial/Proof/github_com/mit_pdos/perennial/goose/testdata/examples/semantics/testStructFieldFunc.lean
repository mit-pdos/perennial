/-
The proof of `testStructFieldFunc` (a goose semantics test, `structs.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructFieldFunc

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructFieldFunc.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testStructFieldFunc.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- the stored function literal is a raw `RecV`
  steps

end proof

end Perennial
