/-
Proofs of the goose semantics tests for method values: `x.M` saves its receiver
when it is evaluated (a copy of it for a value-receiver method, the pointer for
a pointer-receiver one), and calls of the method value use the saved receiver.
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

theorem wp_testMethodValueCopiesReceiver : TestFunOk (GF := GF) testMethodValueCopiesReceiver := by
  semantics_auto

theorem wp_testMethodValuePointerReceiver : TestFunOk (GF := GF) testMethodValuePointerReceiver := by
  semantics_auto

theorem wp_testMethodValueThroughPointer : TestFunOk (GF := GF) testMethodValueThroughPointer := by
  semantics_auto

theorem wp_testMethodValueEmbedded : TestFunOk (GF := GF) testMethodValueEmbedded := by
  semantics_auto

theorem wp_testMethodValueEmbeddedPointer : TestFunOk (GF := GF) testMethodValueEmbeddedPointer := by
  semantics_auto

theorem wp_testMethodValueDefer : TestFunOk (GF := GF) testMethodValueDefer := by
  semantics_auto

theorem wp_testMethodValueDeferArg : TestFunOk (GF := GF) testMethodValueDeferArg := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
