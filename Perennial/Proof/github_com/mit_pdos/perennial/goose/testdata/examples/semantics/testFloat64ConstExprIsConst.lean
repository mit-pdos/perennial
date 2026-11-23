/-
The proof of `testFloat64ConstExprIsConst` (a goose semantics test, `conversions.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloat64ConstExprIsConst

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloat64ConstExprIsConst.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloat64ConstExprIsConst.spec (GF := GF) (hG := hG) := by
  have h : (float64Leb (W64 0) (W64 0x7ff0000000000000) &&
      !float64Eq (W64 0x7ff0000000000000) (W64 0)) = true := by decide +kernel
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  wp_apply wp_float64_div as %f %Hf
  obtain rfl := float64Encodes_eq (b := W64 0x7ff0000000000000) (by decide +kernel) Hf
  rw [h]
  steps
  wp_apply wp_float64_div as %f %Hf
  obtain rfl := float64Encodes_eq (b := W64 0x7ff0000000000000) (by decide +kernel) Hf
  steps
  rw [h]
  iexact HΦ

end proof

end Perennial
