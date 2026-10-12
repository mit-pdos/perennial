/-
The proof of `testCompareSliceToNil` (a goose semantics test, `nil.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testCompareSliceToNil.spec (GF := GF) (hG := hG) := by
  -- allocations are non-nil: `steps` unfolds
  -- `make([]byte, 0)`, which allocates at an arbitrary offset of block 1.
  semantics_auto
  wp_apply wp_ArbitraryInt with %x _
  steps
  have h : ¬ slice.mk ({ locCar := 1, locOff := 0 } +ₗ sint.Z x) (W64 0) (W64 0) = slice.nil := by
    intro h; injection h with h1; simp [Loc.add, null] at h1
  simp only [h, decide_false, Bool.not_false]
  iexact HΦ

end proof

end Perennial
