/-
The proof of `unsafeAdd`: `unsafe.Add`'s pointer addition.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd.spec (GF := GF) (hG := hG) := by
  intro base off
  wp_start as %H
  wp_auto
  wp_func_call
  wp_call
  wp_apply wp_pointer_plus _ _ _ H
  iapply HΦ
  itrivial

end proof

end Perennial
