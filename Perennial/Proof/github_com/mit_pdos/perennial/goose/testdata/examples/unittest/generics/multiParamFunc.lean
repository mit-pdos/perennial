/-
The proof of `generics.multiParamFunc`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.multiParamFunc

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.multiParamFunc.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.multiParamFunc.spec
      (GF := GF) (hG := hG) := by
  intro A' _ _ A _ B' _ _ B _ x y
  wp_start
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_auto
  iapply HΦ
  iExactEq Hsl
  rfl

end proof

end Perennial
