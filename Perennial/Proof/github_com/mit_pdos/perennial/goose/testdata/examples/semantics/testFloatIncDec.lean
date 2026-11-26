/-
The proof of `testFloatIncDec` (a goose semantics test, `float_incdec.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloatIncDec
public import Perennial.Golang.Theory.Float

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloatIncDec.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.testFloatIncDec.spec (GF := GF) (hG := hG) := by
  semantics_auto
  -- each `++`/`--` adds or subtracts 1.0; the result is not a NaN, so its bit pattern is determined
  wp_apply wp_float64_add as %f %Hf
  obtain rfl := float64Encodes_eq (b := W64 0x4004000000000000) (by decide +kernel) Hf
  steps
  wp_apply wp_float32_sub as %g %Hg
  obtain rfl := float32Encodes_eq (b := W32 0xC0500000) (by decide +kernel) Hg
  steps
  wp_apply wp_float64_add as %h1 %Hh1
  obtain rfl := float64Encodes_eq (b := W64 0x3FF8000000000000) (by decide +kernel) Hh1
  steps
  wp_apply wp_float64_sub as %h2 %Hh2
  obtain rfl := float64Encodes_eq (b := W64 0x3FE0000000000000) (by decide +kernel) Hh2
  steps
  wp_apply wp_float64_add as %h3 %Hh3
  obtain rfl := float64Encodes_eq (b := W64 0x3FF8000000000000) (by decide +kernel) Hh3
  steps
  -- each `&&` operand is a closed `float64Eq`/`float32Eq`, which the kernel evaluates to `true`
  repeat
    first
    | generalize hc : float64Eq _ _ = c
      obtain rfl : c = true
      · subst hc; decide +kernel
      steps
    | generalize hc : float32Eq _ _ = c
      obtain rfl : c = true
      · subst hc; decide +kernel
      steps
  iexact HΦ

end proof

end Perennial
