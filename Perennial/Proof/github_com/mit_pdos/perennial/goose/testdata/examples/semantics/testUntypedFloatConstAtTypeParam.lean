/-
The proof of `testUntypedFloatConstAtTypeParam` (a goose semantics test, `conversions.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConstAtTypeParam

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConstAtTypeParam.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConstAtTypeParam.spec (GF := GF) (hG := hG) := by
  have h1 : ratToFloat32 (mkRat 1152921573326323713 1152921504606846976) = W32 0x3f800001 := by
    decide +kernel
  have h2 : float32Eq (W32 0x3f800001) (W32 0x3f800001) = true := by decide +kernel
  have h3 : ratToFloat32 (mkRat (-1) (10 ^ 50)) = W32 0 := by decide +kernel
  have h4 : (float32Leb (W32 0) (W32 0x7f800000) && !float32Eq (W32 0x7f800000) (W32 0)) = true :=
    by decide +kernel
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  simp only [h1, h2]
  steps
  simp only [h1, h2]
  steps
  simp only [h3]
  wp_apply wp_float32_div as %f %Hf
  obtain rfl := float32Encodes_eq (b := W32 0x7f800000) (by decide +kernel) Hf
  rw [h4]
  steps
  simp only [h3]
  wp_apply wp_float32_div as %f %Hf
  obtain rfl := float32Encodes_eq (b := W32 0x7f800000) (by decide +kernel) Hf
  steps
  rw [h4]
  iexact HΦ

end proof

end Perennial
