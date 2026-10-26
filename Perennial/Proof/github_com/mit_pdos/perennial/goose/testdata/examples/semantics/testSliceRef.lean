/-
The proof of `testSliceRef` (a goose semantics test, `slices.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testSliceRef

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testSliceRef.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testSliceRef.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- TODO: `steps` should apply `wp_slice_make2` instead of unfolding it?
  simp only [sliceIndexRef]
  icases array_acc (GF := GF) _ (sint.Z (W64 0)) _ _ _ (zero_val w64) (by decide) rfl $$ p with ⟨Hp0, p⟩
  steps
  simp only [sliceIndexRef]
  steps
  iexact HΦ

end proof

end Perennial
