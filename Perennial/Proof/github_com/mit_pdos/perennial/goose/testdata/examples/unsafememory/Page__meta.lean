/-
The proof of `(*Page).meta`: the meta is 16 bytes past the page.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__meta
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.«meta».wp_proof
    (wp_unsafeAdd : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeAdd.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.«meta».spec (GF := GF) (hG := hG) := by
  intro p
  wp_start as %H
  wp_auto
  wp_apply wp_unsafeAdd
  · ipureintro; rw [show sint.Z (W64 16) = 16 from rfl]; simp only [Loc.add]; omega
  rw [show sint.Z (W64 16) = 16 from rfl]
  iapply HΦ
  itrivial

end proof

end Perennial
