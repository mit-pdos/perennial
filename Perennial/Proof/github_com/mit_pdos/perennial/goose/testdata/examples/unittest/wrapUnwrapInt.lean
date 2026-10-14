/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.wrapUnwrapInt`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.wrapUnwrapInt
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.typeAssertInt

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.wrapUnwrapInt.wp_proof
    (wp_typeAssertInt : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.typeAssertInt.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.wrapUnwrapInt.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply wp_typeAssertInt
  · ipureintro; rfl
  -- the continuation was not introduced since `v` was still a metavariable
  iintro _
  wp_end

end proof

end Perennial
