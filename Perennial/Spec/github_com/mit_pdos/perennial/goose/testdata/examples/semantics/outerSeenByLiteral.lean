/-
`outerSeenByLiteral`'s spec (a goose semantics test, `recover_deferred.go`).
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

/-- `outerSeenByLiteral`: a deferred literal that defers a recovering function and a recovering literal (so it binds its own `$panic`) reads the deferring function's cell through `$recover`, recovers 1 and stores 10; its own deferred calls get `nil`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.outerSeenByLiteral.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! outerSeenByLiteral)) (Val #()))
  {{ RET #(W64 10); True }}

end spec

end Perennial
