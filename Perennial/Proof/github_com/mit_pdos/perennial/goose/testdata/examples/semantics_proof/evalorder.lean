/-
Proofs of the evaluation-order tests of the goose `semantics` test package
(`x op= y` and `x++`). The map tests of `evalorder.go`
(`testOpAssignMapOnce`, `testOpAssignMapReadsAfterRhs`, `testOpAssignMapReadAfterRhs`) are checked by the Go
test suite only, like the other map tests.
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

theorem wp_testOpAssignIndexOnce : TestFunOk (GF := GF) testOpAssignIndexOnce := by
  semantics_auto
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  simp only [show (sint.Z (W64 0)).toNat = 0 from rfl, List.set_cons_zero]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ _ (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha1, a⟩
  steps
  iexact HΦ

theorem wp_testIncIndexOnce : TestFunOk (GF := GF) testIncIndexOnce := by
  semantics_auto
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  simp only [show (sint.Z (W64 0)).toNat = 0 from rfl, List.set_cons_zero]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ _ (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  icases array_acc (GF := GF) _ (sint.Z (W64 1)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha1, a⟩
  steps
  iexact HΦ

theorem wp_testOpAssignReadsAfterRhs : TestFunOk (GF := GF) testOpAssignReadsAfterRhs := by
  semantics_auto

theorem wp_testIncDecNarrow : TestFunOk (GF := GF) testIncDecNarrow := by
  semantics_auto

theorem wp_testIncGeneric : TestFunOk (GF := GF) testIncGeneric := by
  semantics_auto

theorem wp_testOpAssignIndexReadAfterRhs :
    TestFunOk (GF := GF) testOpAssignIndexReadAfterRhs := by
  semantics_auto
  icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ _ (W64 3) (by decide) rfl $$ a with ⟨Ha2, a⟩
  steps
  ihave a := a $$ Ha2
  simp only [show (sint.Z (W64 2)).toNat = 2 from rfl, List.set_cons_succ, List.set_cons_zero]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (W64 1) (by decide) rfl $$ a with ⟨Ha0, a⟩
  steps
  ihave a := a $$ Ha0
  icases array_acc (GF := GF) _ (sint.Z (W64 2)) _ _ _ _ (by decide) rfl $$ a with ⟨Ha2, a⟩
  steps
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
