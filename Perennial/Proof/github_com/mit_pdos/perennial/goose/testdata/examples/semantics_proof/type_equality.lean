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
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testPrimitiveTypesEqual : TestFunOk (GF := GF) testPrimitiveTypesEqual := by
  semantics_auto

theorem wp_testDefinedStrTypesEqual : TestFunOk (GF := GF) testDefinedStrTypesEqual := by
  semantics_auto

theorem wp_testListTypesEqual : TestFunOk (GF := GF) testListTypesEqual := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
