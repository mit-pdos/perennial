/-
`breakLoopFromSwitch`'s spec (a goose semantics test, `labels.go`).
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

/-- `break L` in a `switch` ends the labeled `for`; the unlabeled `break` ends only the `switch`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.breakLoopFromSwitch.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! breakLoopFromSwitch)) (Val #()))
  {{ RET #(W64 2); True }}

end spec

end Perennial
