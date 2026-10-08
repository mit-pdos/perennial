import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testParamsInterface : TestFunOk (GF := GF) testParamsInterface := by
  semantics_auto

theorem wp_testEmptyInterface : TestFunOk (GF := GF) testEmptyInterface := by
  semantics_auto

theorem wp_testTypeAssertionInterface : TestFunOk (GF := GF) testTypeAssertionInterface := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
