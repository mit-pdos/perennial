/-
`topRecover`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `topRecover`: the deferred top-level function `catchTop(&x)` recovers 8 into the named result. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.topRecover.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! topRecover)) (Val #()))
  {{ RET #(W64 8); True }}

end spec

end Perennial
