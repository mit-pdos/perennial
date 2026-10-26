/-
`catchTwoDeep`'s spec (a goose semantics test, `recover.go`).
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

/-- `catchTwoDeep`: the panic raised two calls down, inside a loop, unwinds to the
`Catch` of `catchTwoDeep`'s `defer`, whose literal recovers it and sets the named
result. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.catchTwoDeep.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! catchTwoDeep)) (Val #()))
  {{ RET #true; True }}

end spec

end Perennial
