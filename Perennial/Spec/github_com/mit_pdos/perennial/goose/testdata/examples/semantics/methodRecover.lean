/-
`methodRecover`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `methodRecover`: the deferred method `c.catch(&x)` recovers 7 (`defer` passes it the `$panic` cell) into the named result, which the function returns. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.methodRecover.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! methodRecover)) (Val #()))
  {{ RET #(W64 7); True }}

end spec

end Perennial
