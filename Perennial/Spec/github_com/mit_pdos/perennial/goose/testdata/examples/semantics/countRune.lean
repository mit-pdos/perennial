/-
`countRune`'s spec (a goose semantics test, `range_string.go`).
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

/-- `countRune(s, x)` returns the number of runes of `s` that are `x`: the iterations
of a range loop over `s` (`go.runes s`) whose value is `x`. -/
abbrev github_com.mit_pdos.perennial.goose.testdata.examples.semantics.countRune.spec : Prop :=
  ∀ (str : GoString) (x : w32),
    {{ (True : IProp GF) }}
      (App (App (Val (@! countRune)) (Val #str)) (Val #x))
    {{ RET #(W64 ((go.runes str).countP (fun p => p.2 = x))); True }}

end spec

end Perennial
