/-
The proof of `generics.useBoxGet`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useBoxGet
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeGenericBox
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useBoxGet.wp_proof
    (wp_makeGenericBox :
      github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.makeGenericBox.spec
        (GF := GF) (hG := hG))
    (wp_Box_Get :
      github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.Box.Get.spec
        (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unittest.generics.useBoxGet.spec
      (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_makeGenericBox
  wp_apply wp_Box_Get $$ [$]
  wp_end

end proof

end Perennial
