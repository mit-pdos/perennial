/-
The proof of `(*Page).leafPageElement`: element `i` is `16 + 16 i` bytes past the page.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeIndex

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.wp_proof
    (wp_unsafeIndex : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.unsafeIndex.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.spec (GF := GF) (hG := hG) := by
  intro p idx
  wp_start as %H
  simp only [leafPageElementSize]
  wp_auto
  have hz : sint.Z (W64 16 + W64 (uint.Z idx) * W64 16) = 16 + 16 * uint.Z idx := by
    have := idx.isLt; simp only [uint.Z] at *; word
  have hi : 0 ≤ uint.Z idx := by simp [uint.Z]
  wp_apply wp_unsafeIndex
  · ipureintro; rw [hz]; simp only [Loc.add]; omega
  rw [hz]
  iapply HΦ
  itrivial

end proof

end Perennial
