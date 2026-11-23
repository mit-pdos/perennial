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
  have h1 : ratToFloat64 (mkRat 1152921573326323713 1152921504606846976) = W64 0x3ff0000010000000 :=
    by decide +kernel
  have h2 : float64Eq (W64 0x3ff0000010000000) (W64 0x3ff0000010000000) = true := by decide +kernel
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  steps
  simp only [h1, h2]
  steps
  simp only [h1, h2]
  iexact HΦ

/-- `T(c)` at a type parameter instantiated with `float32` rounds the exact constant once (the
spec's reading; gc gives `0x3f800000`, `docs/KNOWN_LIMITATIONS.md`): `0x3f800001`. -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.offTieConvertedAt_float32
    (Φ : val → IProp GF) :
    ⊢ Φ #(W32 0x3f800001) -∗
      WP (App (App (Val (GoInstruction (FuncResolve offTieConvertedAt [go.float32]))) (Val #()))
        (Val #())) {{ Φ }} := by
  have h1 : ratToFloat32 (mkRat 1152921573326323713 1152921504606846976) = W32 0x3f800001 :=
    by decide +kernel
  iintro HΦ
  steps
  simp only [h1]
  iexact HΦ

end proof

end Perennial
