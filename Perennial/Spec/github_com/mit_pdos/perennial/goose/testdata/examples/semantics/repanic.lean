/-
`repanic`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `repanic`: the panic 6 that the deferred method raises again is recovered by the caller's deferred literal: 6*10 + 1. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.repanic.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! repanic)) (Val #()))
  {{ RET #(W64 61); True }}

end spec

end Perennial
