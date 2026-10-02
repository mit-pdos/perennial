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

theorem wp_testMinUint64 : test_fun_ok (GF := GF) testMinUint64 := by
  semantics_auto
  -- the `FuncUnfold go.min (List.replicate n t)` instance does not match `[t, t]`
  rw [show ([go.uint64, go.uint64] : List go.type) = List.replicate 2 go.uint64 from rfl,
    func_unfold (f := go.min)]
  steps
  iexact HΦ

theorem wp_testMaxUint64 : test_fun_ok (GF := GF) testMaxUint64 := by
  semantics_auto
  -- the `FuncUnfold go.max (List.replicate n t)` instance does not match `[t, t]`
  rw [show ([go.uint64, go.uint64] : List go.type) = List.replicate 2 go.uint64 from rfl,
    func_unfold (f := go.max)]
  steps
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
