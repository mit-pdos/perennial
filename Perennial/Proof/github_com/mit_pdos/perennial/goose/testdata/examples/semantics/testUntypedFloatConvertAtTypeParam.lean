/-
The proof of `testUntypedFloatConvertAtTypeParam` (a goose semantics test, `conversions.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConvertAtTypeParam

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConvertAtTypeParam.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testUntypedFloatConvertAtTypeParam.spec (GF := GF) (hG := hG) := by
  have h1 : float32Eq (W32 0x3f800000) (W32 0x3f800000) = true := by decide +kernel
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  wp_apply wp_float64_to_float32 as %f %Hf
  obtain rfl := float32Encodes_eq (b := W32 0x3f800000) (by decide +kernel) Hf
  rw [h1]
  steps
  wp_apply wp_float64_to_float32 as %f %Hf
  obtain rfl := float32Encodes_eq (b := W32 0x3f800000) (by decide +kernel) Hf
  steps
  rw [h1]
  iexact HΦ

end proof

end Perennial
