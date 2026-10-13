/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.useFloat`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useFloat

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useFloat.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useFloat.spec (GF := GF) (hG := hG) := by
  wp_start
  -- the package constant `a` (a `def` of type `val`) must be unfolded
  simp only [a]
  wp_auto
  -- the sum and the product: any NaN when they are NaNs (`go.floatResult64`)
  wp_bind (go.floatResult64 _)
  iapply wp_floatResult64; iintro %f
  wp_auto
  wp_bind (go.floatResult64 _)
  iapply wp_floatResult64; iintro %g
  wp_auto
  wp_end

end proof

end Perennial
