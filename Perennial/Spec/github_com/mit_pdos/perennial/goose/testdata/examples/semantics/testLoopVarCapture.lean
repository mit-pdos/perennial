/-
`testLoopVarCapture`'s spec (a goose semantics test, `loopvars.go`).
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- The closure stored in iteration 1 reads iteration 1's own variable, which
keeps the value 1 (the loop increments the next iteration's copy). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testLoopVarCapture.spec : Prop :=
  TestFunOk (GF := GF) testLoopVarCapture

end spec

end Perennial
