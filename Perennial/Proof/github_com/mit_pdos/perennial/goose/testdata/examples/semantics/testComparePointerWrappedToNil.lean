/-
The proof of `testComparePointerWrappedToNil` (a goose semantics test, `nil.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerWrappedToNil

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerWrappedToNil.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testComparePointerWrappedToNil.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- the slice has length 1, so it is not nil
  have h : ¬ slice.mk p_ptr (W64 1) (W64 1) = slice.nil := by
    intro h; injection h with _ h2; exact absurd h2 (by decide)
  simp only [h, decide_false, Bool.not_false]
  iexact HΦ

end proof

end Perennial
