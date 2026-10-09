/-
Proofs of the goose semantics tests for comparisons with `nil`.
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
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testCompareNilToNil : TestFunOk (GF := GF) testCompareNilToNil := by
  semantics_auto

theorem wp_testComparePointerWrappedDefaultToNil : TestFunOk (GF := GF) testComparePointerWrappedDefaultToNil := by
  semantics_auto

theorem wp_testInterfaceNilWithType : TestFunOk (GF := GF) testInterfaceNilWithType := by
  semantics_auto

theorem wp_testComparePointerToNil : TestFunOk (GF := GF) testComparePointerToNil := by
  semantics_auto
  -- points-tos are non-null: `typedPointsto_not_null`
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$r0»
  simp only [Hnn, decide_false, Bool.not_false]
  iexact HΦ

theorem wp_testComparePointerWrappedToNil : TestFunOk (GF := GF) testComparePointerWrappedToNil := by
  semantics_auto
  -- the slice has length 1, so it is not nil
  have h : ¬ slice.mk p_ptr (W64 1) (W64 1) = slice.nil := by
    intro h; injection h with _ h2; exact absurd h2 (by decide)
  simp only [h, decide_false, Bool.not_false]
  iexact HΦ

theorem wp_testCompareSliceToNil : TestFunOk (GF := GF) testCompareSliceToNil := by
  -- allocations are non-nil: `steps` unfolds
  -- `make([]byte, 0)`, which allocates at an arbitrary offset of block 1.
  semantics_auto
  wp_apply wp_ArbitraryInt with %x _
  steps
  have h : ¬ slice.mk ({ locCar := 1, locOff := 0 } +ₗ sint.Z x) (W64 0) (W64 0) = slice.nil := by
    intro h; injection h with h1; simp [Loc.add, null] at h1
  simp only [h, decide_false, Bool.not_false]
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
