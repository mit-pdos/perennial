/-
Proofs of the operator-precedence tests of the goose `semantics` test package.
-/
module

public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testOrCompare : TestFunOk (GF := GF) testOrCompare := by
  semantics_auto

theorem wp_testAndCompare : TestFunOk (GF := GF) testAndCompare := by
  semantics_auto

theorem wp_testShiftMod : TestFunOk (GF := GF) testShiftMod := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
