/-
`continueFromNestedSwitch`'s spec (a goose semantics test, `labels.go`).
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

/-- `doPrintf`'s shape: `continue L` from a `switch` in a `switch` in an inner `for`, whose post statement does not run. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.continueFromNestedSwitch.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! continueFromNestedSwitch)) (Val #()))
  {{ RET #(W64 3); True }}

end spec

end Perennial
