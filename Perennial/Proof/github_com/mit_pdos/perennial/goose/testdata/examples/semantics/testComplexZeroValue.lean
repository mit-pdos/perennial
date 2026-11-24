/-
The proof of `testComplexZeroValue` (a goose semantics test, `complex_types.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComplexZeroValue

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComplexZeroValue.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComplexZeroValue.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- each `==` of complex zero values is a closed float `==`, which the kernel evaluates to `true`
  repeat
    first
    | generalize hc : float32Eq _ _ = c
      obtain rfl : c = true
      · subst hc; decide +kernel
    | generalize hc : float64Eq _ _ = c
      obtain rfl : c = true
      · subst hc; decide +kernel
    steps
  iexact HΦ

end proof

end Perennial
