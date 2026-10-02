/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/type_equality.v`.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testPrimitiveTypesEqual : test_fun_ok (GF := GF) testPrimitiveTypesEqual := by
  semantics_auto

theorem wp_testDefinedStrTypesEqual : test_fun_ok (GF := GF) testDefinedStrTypesEqual := by
  semantics_auto

theorem wp_testListTypesEqual : test_fun_ok (GF := GF) testListTypesEqual := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
