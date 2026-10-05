/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/semantics_proof/structs.v`.
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

omit package_sem in
/-- Two full points-tos for the same `w64` location are contradictory. -/
theorem w64_pointsto_excl (l : loc) (v w : w64) :
    (typed_pointsto l v (DFrac.own 1) : IProp GF) ∗ typed_pointsto l w (DFrac.own 1) ⊢ False := by
  rw [typed_pointsto_unseal]; unfold typedPointstoWrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  have e : ∀ u : w64, typed_pointsto_def (GF := GF) l u (DFrac.own 1) =
      heapPointsto l (DFrac.own 1) #u := fun _ => rfl
  simp only [e]
  icombine H1 H2 gives % ⟨Hv, _⟩
  exact absurd (DFrac.valid_op_own Hv) (by simp)

theorem wp_testStructUpdates : TestFunOk (GF := GF) testStructUpdates := by
  semantics_auto

theorem wp_testNestedStructUpdates : TestFunOk (GF := GF) testNestedStructUpdates := by
  semantics_auto

theorem wp_testStructConstructions : TestFunOk (GF := GF) testStructConstructions := by
  semantics_auto
  by_cases h : p4_ptr = «$r0_ptr»
  · -- Rocq: Admitted ("how to combine typed_pointsto to get sum of fractions?")
    subst h
    iexfalso
    rw [typed_pointsto_unseal_eq p4_ptr (_ : TwoInts.t), typed_pointsto_unseal_eq p4_ptr (_ : TwoInts.t)]
    simp only [TypedPointsto.typed_pointsto_def]
    icases p4 with ⟨⟨Hx, _⟩, _⟩
    icases «$r0» with ⟨⟨Hx', _⟩, _⟩
    iapply w64_pointsto_excl
    iframe
  · simp only [h, decide_false, Bool.not_false]
    iexact HΦ

theorem wp_testIncompleteStruct : TestFunOk (GF := GF) testIncompleteStruct := by
  semantics_auto

theorem wp_testStoreInStructVar : TestFunOk (GF := GF) testStoreInStructVar := by
  semantics_auto

theorem wp_testStoreInStructPointerVar : TestFunOk (GF := GF) testStoreInStructPointerVar := by
  semantics_auto

theorem wp_testStoreComposite : TestFunOk (GF := GF) testStoreComposite := by
  semantics_auto

theorem wp_testStoreSlice : TestFunOk (GF := GF) testStoreSlice := by
  semantics_auto

theorem wp_testStructFieldFunc : TestFunOk (GF := GF) testStructFieldFunc := by
  semantics_auto
  -- the stored function literal is a raw `RecV`
  steps

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
