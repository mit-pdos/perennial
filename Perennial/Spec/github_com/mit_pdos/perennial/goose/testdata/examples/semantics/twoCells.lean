/-
`twoCells`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `twoCells`: 4 is recovered by the deferred `c.catchTwice(&x)`, and 5 by `catchTwice`'s own deferred literal: 50. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.twoCells.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! twoCells)) (Val #()))
  {{ RET #(W64 50); True }}

end spec

end Perennial
