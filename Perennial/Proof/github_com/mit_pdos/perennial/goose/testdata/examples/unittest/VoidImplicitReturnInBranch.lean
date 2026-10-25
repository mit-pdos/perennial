/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.VoidImplicitReturnInBranch`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidImplicitReturnInBranch
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.BasicNamedReturn

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidImplicitReturnInBranch.wp_proof
    (wp_BasicNamedReturn : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.BasicNamedReturn.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.VoidImplicitReturnInBranch.spec (GF := GF) (hG := hG) := fun b => by
  wp_start
  wp_auto
  cases b
  · wp_auto
    wp_apply wp_BasicNamedReturn
    wp_end
  · wp_auto
    wp_end

end proof

end Perennial
