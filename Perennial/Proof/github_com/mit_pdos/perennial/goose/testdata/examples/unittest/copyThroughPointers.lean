/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.copyThroughPointers`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.copyThroughPointers

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.copyThroughPointers.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.copyThroughPointers.spec (GF := GF) (hG := hG) := by
  intro p q v w dq hov
  wp_start as ⟨Hp, Hq⟩
  wp_auto
  wp_apply wp_check_copy bigStruct.ty p q hov
  iapply HΦ
  iframe

end proof

end Perennial
