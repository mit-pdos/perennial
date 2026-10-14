/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.useEmbeddedMethod`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useEmbeddedMethod

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useEmbeddedMethod.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.useEmbeddedMethod.spec (GF := GF) (hG := hG) := fun d b => by
  wp_start
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  wp_auto
  wp_method_call
  repeat wp_call
  wp_auto
  wp_method_call
  repeat wp_call
  wp_auto
  iapply HΦ
  itrivial

end proof

end Perennial
