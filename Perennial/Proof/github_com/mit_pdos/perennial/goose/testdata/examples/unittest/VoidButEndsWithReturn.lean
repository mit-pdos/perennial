/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.VoidButEndsWithReturn`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidButEndsWithReturn
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.BasicNamedReturn

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidButEndsWithReturn.wp_proof
    (wp_BasicNamedReturn : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.BasicNamedReturn.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidButEndsWithReturn.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_BasicNamedReturn
  wp_end

end proof

end Perennial
