/-
`countPairs`'s spec (a goose semantics test, `labels.go`).
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

/-- `countPairs(n)` counts the pairs `j < i < n`, with `continue L` ending each inner loop. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countPairs.spec : Prop :=
  ∀ n : w64, uint.Z n < 2 ^ 32 →
    {{ (True : IProp GF) }}
      (App (Val (@! countPairs)) (Val #n))
    {{ RET #(W64 (uint.Z n * (uint.Z n - 1) / 2)); True }}

end spec

end Perennial
