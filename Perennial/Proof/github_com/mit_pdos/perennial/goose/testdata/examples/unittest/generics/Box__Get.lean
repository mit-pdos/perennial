/-
The proof of `generics.(*Box).Get`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Box__Get

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Assumptions]

/-- Loads the box and calls the value-receiver `Box.Get` (the shared `Box.wp_Get'`). -/
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Box.Get.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Box.Get.spec
      (GF := GF) (hG := hG) := by
  intro T' _ _ T _ l b
  wp_start
  wp_auto
  wp_apply Box.wp_Get'
  wp_end

end proof

end Perennial
