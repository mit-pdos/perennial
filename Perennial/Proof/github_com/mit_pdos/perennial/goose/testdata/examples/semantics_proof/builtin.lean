/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/builtin.v`.

The Rocq lemmas end in `Abort` ("TODO: min", "TODO: max"); they are proved here.
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

theorem wp_testMinUint64 : TestFunOk (GF := GF) testMinUint64 := by
  semantics_auto

theorem wp_testMaxUint64 : TestFunOk (GF := GF) testMaxUint64 := by
  semantics_auto

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
