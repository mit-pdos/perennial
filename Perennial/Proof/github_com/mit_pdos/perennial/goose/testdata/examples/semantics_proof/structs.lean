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
  rw [typed_pointsto_unseal]; unfold typed_pointsto_wrap
  iintro ⟨⟨H1, _⟩, ⟨H2, _⟩⟩
  have e : ∀ u : w64, typed_pointsto_def (GF := GF) l u (DFrac.own 1) =
      heap_pointsto l (DFrac.own 1) #u := fun _ => rfl
  simp only [e]
  icombine H1 H2 gives % ⟨Hv, _⟩
  exact absurd (DFrac.valid_op_own Hv) (by simp)

theorem wp_testStructUpdates : test_fun_ok (GF := GF) testStructUpdates := by
  semantics_auto

theorem wp_testNestedStructUpdates : test_fun_ok (GF := GF) testNestedStructUpdates := by
  semantics_auto

theorem wp_testStructConstructions : test_fun_ok (GF := GF) testStructConstructions := by
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

theorem wp_testIncompleteStruct : test_fun_ok (GF := GF) testIncompleteStruct := by
  semantics_auto

theorem wp_testStoreInStructVar : test_fun_ok (GF := GF) testStoreInStructVar := by
  semantics_auto

theorem wp_testStoreInStructPointerVar : test_fun_ok (GF := GF) testStoreInStructPointerVar := by
  semantics_auto

theorem wp_testStoreComposite : test_fun_ok (GF := GF) testStoreComposite := by
  semantics_auto

theorem wp_testStoreSlice : test_fun_ok (GF := GF) testStoreSlice := by
  semantics_auto

theorem wp_testStructFieldFunc : test_fun_ok (GF := GF) testStructFieldFunc := by
  semantics_auto
  -- the stored function literal is a raw `RecV`
  rw [recv_eq_func]
  steps
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
