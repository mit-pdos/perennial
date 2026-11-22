/-
The proof of `testIntToFloat64` (a goose semantics test, `conversions.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testIntToFloat64

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testIntToFloat64.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testIntToFloat64.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- each `&&` operand is a closed `float64Eq`, which the kernel evaluates to `true`
  repeat
    generalize hc : float64Eq _ _ = c
    obtain rfl : c = true
    · subst hc; decide +kernel
    steps
  iexact HΦ

end proof

end Perennial
