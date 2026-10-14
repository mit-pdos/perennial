/-
`testRecoverInLoop`'s spec (a goose semantics test, `recover.go`).
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

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRecoverInLoop.spec : Prop :=
  TestFunOk (GF := GF) testRecoverInLoop

end spec

end Perennial
