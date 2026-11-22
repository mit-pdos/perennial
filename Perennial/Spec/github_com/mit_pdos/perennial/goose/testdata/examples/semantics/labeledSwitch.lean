/-
`labeledSwitch`'s spec (a goose semantics test, `labels.go`).
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

/-- `break L` of a labeled `switch`, from a `for` in a case, skips the rest of the case. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.labeledSwitch.spec : Prop :=
  ∀ x : w64,
    {{ (True : IProp GF) }}
      (App (Val (@! labeledSwitch)) (Val #x))
    {{ RET #(if x = W64 1 then W64 2 else W64 50); True }}

end spec

end Perennial
