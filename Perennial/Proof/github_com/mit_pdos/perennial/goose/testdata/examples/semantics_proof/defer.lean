/-
Proofs of the goose semantics tests for the results of a function that defers:
`return e` assigns the results, the deferred functions run (and may read and
modify the named results), and the function returns the results' final values.
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

theorem wp_testDeferAssignResult : TestFunOk (GF := GF) testDeferAssignResult := by
  semantics_auto

theorem wp_testDeferIncrResult : TestFunOk (GF := GF) testDeferIncrResult := by
  semantics_auto

theorem wp_testDeferRecoverResult : TestFunOk (GF := GF) testDeferRecoverResult := by
  semantics_auto

theorem wp_testDeferReadResult : TestFunOk (GF := GF) testDeferReadResult := by
  semantics_auto

theorem wp_testDeferUnnamedResults : TestFunOk (GF := GF) testDeferUnnamedResults := by
  semantics_auto

theorem wp_testDeferShadowedResult : TestFunOk (GF := GF) testDeferShadowedResult := by
  semantics_auto

theorem wp_testDeferSwapResults : TestFunOk (GF := GF) testDeferSwapResults := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
