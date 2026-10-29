/-
`testOverlappingCopyViaTemp`'s spec (`goose/testdata/examples/unsafememory`).
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Layout

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
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Assumptions]

abbrev github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingCopyViaTemp.spec : Prop :=
  github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.TestFunOk (GF := GF) github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingCopyViaTemp

end spec

end Perennial
