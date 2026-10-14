/-
`testRangeArrayLit`'s spec (a goose semantics test, `arrays.go`).
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

/-- `for i, x := range [3]uint64{1, 2, 3}` adds `x + i` to `sum`; `j` counts
the iterations (the loop's own counter). -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testRangeArrayLit.spec : Prop :=
  TestFunOk (GF := GF) testRangeArrayLit

end spec

end Perennial
