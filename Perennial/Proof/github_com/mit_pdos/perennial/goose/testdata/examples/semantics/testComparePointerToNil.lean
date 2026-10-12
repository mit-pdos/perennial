/-
The proof of `testComparePointerToNil` (a goose semantics test, `nil.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerToNil

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerToNil.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerToNil.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- points-tos are non-null: `typedPointsto_not_null`
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  simp only [Hnn, decide_false, Bool.not_false]
  iexact HΦ

end proof

end Perennial
