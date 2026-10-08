/-
Semantics tests for integer conversions.
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

theorem wp_testU64ToU32 : TestFunOk (GF := GF) testU64ToU32 := by
  semantics_auto

theorem wp_testU32ToU64 : TestFunOk (GF := GF) testU32ToU64 := by
  semantics_auto

theorem wp_testU32Len : TestFunOk (GF := GF) testU32Len := by
  semantics_auto

theorem wp_testU32NewtypeLen : TestFunOk (GF := GF) testU32NewtypeLen := by
  semantics_auto

theorem wp_testUint32Untyped : TestFunOk (GF := GF) testUint32Untyped := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
