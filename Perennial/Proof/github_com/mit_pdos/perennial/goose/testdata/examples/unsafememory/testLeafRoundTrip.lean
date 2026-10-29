/-
The proof of `testLeafRoundTrip`: a leaf page written over a zeroed buffer reads back its inodes.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testLeafRoundTrip
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf
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

set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testLeafRoundTrip.wp_proof
    (wp_leafInodes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.spec (GF := GF) (hG := hG))
    (wp_writeLeaf : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.spec (GF := GF) (hG := hG))
    (wp_readInodeFromPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.spec (GF := GF) (hG := hG))
    (wp_inodesEqual : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testLeafRoundTrip.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro #Hpkg HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_leafInodes as %s #Hin
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
  have hbody := leafModel_body_length true
  wp_apply wp_writeLeaf buf s leafModel 4096 $$ [Hb] as Hb
  · iframe Hb Hin; ipureintro; exact ⟨hbufW, by decide, leafModel_fits, by rw [hbody]; omega⟩
  imod bytesPointsto_persist _ _ _ $$ Hb with #Hb
  rw [List.append_assoc]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨#Hh, #Hb⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (ByteEncoding.encode_length _) Hbp).1 $$ Hh with #Hh
  rw [ByteEncoding.decode_encode, ByteEncoding.encode_length,
    show ((16 : Nat) : Int) = (16 : Int) from rfl]
  wp_apply wp_readInodeFromPage buf.ptr (leafHeader leafModel) leafModel _ as %out #Hout
  · rw [pageIsLeaf_leafHeader]
    iframe Hh Hb; ipureintro; exact ⟨Hbp, rfl, leafModel_fits⟩
  wp_apply wp_inodesEqual out s _ leafModel as -
  · iframe Hout Hin
  have hrb : readBack (pageIsLeaf (leafHeader leafModel)) leafModel = leafModel := by
    rw [pageIsLeaf_leafHeader]; simp [readBack, leafModel]
  rw [hrb, decide_eq_true rfl]
  iexact HΦ

end proof

end Perennial
