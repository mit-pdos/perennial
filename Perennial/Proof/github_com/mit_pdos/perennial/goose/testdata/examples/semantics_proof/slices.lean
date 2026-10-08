/-
Semantics tests for slices.
-/
import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.semantics_proof.semantics_init

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics

section wps
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics] [package_sem : semantics.Assumptions]

theorem wp_testSliceRef : TestFunOk (GF := GF) testSliceRef := by
  semantics_auto
  -- TODO: `steps` should apply `wp_slice_make2` instead of unfolding it?
  simp only [sliceIndexRef]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (zero_val w64) (by decide) rfl $$ p with ⟨Hp0, p⟩
  steps
  simp only [sliceIndexRef]
  steps
  iexact HΦ

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics

end Perennial
