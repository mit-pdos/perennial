/-
The proof of `github.com/mit-pdos/perennial/goose/testdata/examples/unittest.Point.IgnoreReceiver`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Point__IgnoreReceiver

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.unittest

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Point.IgnoreReceiver.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.Point.IgnoreReceiver.spec (GF := GF) (hG := hG) := fun p => by
  wp_start
  wp_end

end proof

end Perennial
