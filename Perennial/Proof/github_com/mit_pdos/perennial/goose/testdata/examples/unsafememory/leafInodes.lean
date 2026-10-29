/-
The proof of `leafInodes`: a slice literal of three inodes over fresh byte slices.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes

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

attribute [-instance] go.SliceSemantics.composite_literal_slice
set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes go!"apple" as %s0 ⟨Hs0, -⟩
  wp_apply wp_string_to_bytes go!"1" as %s1 ⟨Hs1, -⟩
  wp_apply wp_string_to_bytes go!"banana" as %s2 ⟨Hs2, -⟩
  wp_apply wp_string_to_bytes go!"22" as %s3 ⟨Hs3, -⟩
  wp_apply wp_string_to_bytes go!"cherry" as %s4 ⟨Hs4, -⟩
  wp_apply wp_slice_literal (V := w8) []
  isplitr
  · ipureintro; rfl
  iintro %s5p ⟨Hs5, -⟩
  wp_auto
  wp_apply wp_slice_literal (V := inode)
    [⟨0, 0, s0, s1⟩, ⟨0, 0, s2, s3⟩,
     ⟨0, 0, s4, slice.mk s5p (W64 (go.arrayLiteralSize [])) (W64 (go.arrayLiteralSize []))⟩]
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  ipersist Hs0
  ipersist Hs1
  ipersist Hs2
  ipersist Hs3
  ipersist Hs4
  ipersist Hs5
  ipersist Hs
  wp_auto
  iapply HΦ
  unfold inodesOwn leafModel
  iexists _
  iframe Hs
  iapply BigSepL2.bigSepL2_cons.2
  isplitr
  · unfold inodeOwn; iframe Hs0 Hs1; ipureintro; exact ⟨rfl, rfl⟩
  iapply BigSepL2.bigSepL2_cons.2
  isplitr
  · unfold inodeOwn; iframe Hs2 Hs3; ipureintro; exact ⟨rfl, rfl⟩
  iapply BigSepL2.bigSepL2_cons.2
  isplitr
  · unfold inodeOwn; iframe Hs4 Hs5; ipureintro; exact ⟨rfl, rfl⟩
  iapply BigSepL2.bigSepL2_nil.2
  itrivial

end proof

end Perennial
