/-
The proof of `pageBytes`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeByteSlice

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes.wp_proof
    (wp_unsafeByteSlice : unsafeByteSlice.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes.spec (GF := GF) (hG := hG) := by
  intro p n
  wp_start as %H
  wp_auto
  wp_apply wp_unsafeByteSlice
  · ipureintro; simp; omega
  have h0 : sint.Z (W64 0) = 0 := rfl
  rw [h0, loc_add_0, loc_add_0, show n - W64 0 = n by simp]
  iapply HΦ
  itrivial

end proof

end Perennial
