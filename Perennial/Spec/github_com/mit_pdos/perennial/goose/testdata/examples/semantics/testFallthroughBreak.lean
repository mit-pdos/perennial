/-
`testFallthroughBreak`'s spec (a goose semantics test, `control_flow.go`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section spec
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- Case 0 falls through into case 1, whose `break` ends the `switch`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFallthroughBreak.spec : Prop :=
  TestFunOk (GF := GF) testFallthroughBreak

end spec

end Perennial
