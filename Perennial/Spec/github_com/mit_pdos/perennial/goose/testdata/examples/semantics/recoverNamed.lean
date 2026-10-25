/-
`recoverNamed`'s spec (a goose semantics test, `recover.go`).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

/-- `recoverNamed`: the deferred literal recovers the panic (`recover()` reads and
clears the `$panic` cell) and sets the named result, which the function returns. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.recoverNamed.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! recoverNamed)) (Val #()))
  {{ RET #(W64 42); True }}

end spec

end Perennial
