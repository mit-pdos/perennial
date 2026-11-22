/-
`miniPrintf`'s spec (a goose semantics test, `labels.go`).
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

/-- `doPrintf`'s shape (`continue formatLoop`, `break simpleFormat`) on one format string. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.miniPrintf.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! miniPrintf)) (Val #(go!"x%-vy%3z%")))
  {{ RET (PairV #(go!"xVy!3z!") #(W64 1)); True }}

end spec

end Perennial
