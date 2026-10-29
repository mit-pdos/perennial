/-
The proof of `testBranchRoundTrip`: a branch page, whose elements hold page ids at offset 8, reads back its inodes.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBranchRoundTrip
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual

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

/-- The inodes of `testBranchRoundTrip`. -/
def branchModel : List InodeM := [⟨0, W64 7, go!"a", []⟩, ⟨0, W64 1099511627776, go!"m", []⟩]

theorem branchModel_body_length (leaf : Bool) : (pageBody leaf branchModel).length = 34 := by
  rw [pageBody_length]; simp [dataBytes, branchModel, InodeM.kv]

theorem branchModel_fits : pageFits branchModel := by
  refine ⟨by simp [branchModel], by rw [branchModel_body_length]; omega, ?_⟩
  intro m hm; simp [branchModel] at hm; rcases hm with rfl | rfl <;> simp

set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBranchRoundTrip.wp_proof
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_writeInodeToPage : writeInodeToPage.spec (GF := GF) (hG := hG))
    (wp_readInodeFromPage : readInodeFromPage.spec (GF := GF) (hG := hG))
    (wp_inodesEqual : inodesEqual.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBranchRoundTrip.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro #Hpkg HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_string_to_bytes go!"a" as %s0 ⟨Hs0, -⟩
  wp_apply wp_string_to_bytes go!"m" as %s1 ⟨Hs1, -⟩
  wp_apply wp_slice_literal (V := inode) [⟨0, W64 7, s0, slice.nil⟩, ⟨0, W64 1099511627776, s1, slice.nil⟩]
  isplitr
  · ipureintro; rfl
  iintro %sp ⟨Hs, -⟩
  ipersist Hs0
  ipersist Hs1
  ipersist Hs
  ihave #Hin : inodesOwn (slice.mk sp (W64 (go.arrayLiteralSize _)) (W64 (go.arrayLiteralSize _)))
      branchModel $$ []
  · unfold inodesOwn branchModel
    iexists _
    iframe Hs
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · unfold inodeOwn; iframe Hs0; isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iapply ownSlice_nil
    iapply BigSepL2.bigSepL2_cons.2
    isplitr
    · unfold inodeOwn; iframe Hs1; isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      · iapply ownSlice_nil
    iapply BigSepL2.bigSepL2_nil.2
    itrivial
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  ihave %Hbl := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbp := ownSlice_ptr_pos _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hbuf
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hbp $$ Hbuf
    with ⟨Hb, -⟩
  rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
  rw [List.length_replicate] at Hbl
  have hbufW : buf.len = W64 (4096 : Nat) := w64_of_sint_nat _ _ Hbl.1 Hbl.2
  have hbufZ : sint.Z buf.len = 4096 := by rw [hbufW]; rfl
  ihave %Hbd := bytesPointsto_bounds _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hb
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbp, by decide, ?_⟩; rw [hbufZ]; decide
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0,
    show List.replicate 4096 (0 : w8) = List.replicate 16 0 ++ List.replicate 4080 0 by
      rw [List.replicate_append_replicate]]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hb⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) Hbp).1 $$ Hh with Hh
  wp_auto
  ihave Hh := typedPointsto_of_eq _ _ (⟨0, W16 1, W16 2, 0⟩ : Page) _ $$ [Hh]
  · iframe Hh; ipureintro; rfl
  rw [List.length_replicate, show ((16 : Nat) : Int) = (16 : Int) from rfl]
  have hbody := branchModel_body_length true
  wp_apply wp_writeInodeToPage _ branchModel buf.ptr ⟨0, W16 1, W16 2, 0⟩ 4080 $$ [Hh Hb]
    as %w ⟨Hh, Hb⟩
  · iframe Hh Hb Hin; ipureintro; exact ⟨Hbp, branchModel_fits, by rw [hbody]; omega⟩
  imod typedPointsto_persist_view _ _ _ Hbp $$ Hh with #Hh
  imod bytesPointsto_persist _ _ _ $$ Hb with #Hb
  have hbr : pageIsLeaf (⟨0, W16 1, W16 2, 0⟩ : Page) = false := by
    unfold pageIsLeaf
    have : (W16 1 &&& W16 2 : w16) = W16 0 := by rfl
    exact decide_eq_false (fun h => h this)
  rw [hbr]
  wp_apply wp_readInodeFromPage buf.ptr ⟨0, W16 1, W16 2, 0⟩ branchModel _ as %out #Hout
  · rw [hbr]
    iframe Hh Hb; ipureintro; exact ⟨Hbp, rfl, branchModel_fits⟩
  wp_apply wp_inodesEqual out _ _ branchModel as -
  · iframe Hout Hin
  have hrb : readBack (pageIsLeaf (⟨0, W16 1, W16 2, 0⟩ : Page)) branchModel = branchModel := by
    rw [hbr]; simp [readBack, branchModel]
  rw [hrb, decide_eq_true rfl]
  iexact HΦ

end proof

end Perennial
