/-
The proof of `testSearch`: binary search over the element array of a leaf page.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testSearch
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.searchLeaf

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
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testSearch.wp_proof
    (wp_leafInodes : leafInodes.spec (GF := GF) (hG := hG))
    (wp_writeLeaf : writeLeaf.spec (GF := GF) (hG := hG))
    (wp_searchLeaf : searchLeaf.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testSearch.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro #Hpkg HΦ
  wp_func_call
  wp_call
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
  wp_apply wp_leafInodes as %s #Hin
  have hbody := leafModel_body_length true
  wp_apply wp_writeLeaf buf s leafModel 4096 $$ [Hb] as Hb
  · iframe Hb Hin; ipureintro; exact ⟨hbufW, by decide, leafModel_fits, by rw [hbody]; omega⟩
  imod bytesPointsto_persist _ _ _ $$ Hb with #Hb
  rw [List.append_assoc]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨#Hh, #Hb⟩
  icases (bytesPointsto_typed (V := Page) _ _ _ (ByteEncoding.encode_length _) Hbp).1 $$ Hh with #Hh
  rw [ByteEncoding.decode_encode, ByteEncoding.encode_length,
    show ((16 : Nat) : Int) = (16 : Int) from rfl]
  wp_apply wp_string_to_bytes [] as %k0 ⟨Hk0, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k0 [] (DFrac.own 1) 0 $$ [Hk0]
    as Hk0
  · iframe Hh Hb Hk0
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  wp_apply wp_string_to_bytes go!"apple" as %k1 ⟨Hk1, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k1 go!"apple" (DFrac.own 1) 0 $$ [Hk1]
    as Hk1
  · iframe Hh Hb Hk1
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  wp_apply wp_string_to_bytes go!"b" as %k2 ⟨Hk2, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k2 go!"b" (DFrac.own 1) 1 $$ [Hk2]
    as Hk2
  · iframe Hh Hb Hk2
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  wp_apply wp_string_to_bytes go!"banana" as %k3 ⟨Hk3, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k3 go!"banana" (DFrac.own 1) 1 $$ [Hk3]
    as Hk3
  · iframe Hh Hb Hk3
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  wp_apply wp_string_to_bytes go!"c" as %k4 ⟨Hk4, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k4 go!"c" (DFrac.own 1) 2 $$ [Hk4]
    as Hk4
  · iframe Hh Hb Hk4
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  wp_apply wp_string_to_bytes go!"zzz" as %k5 ⟨Hk5, -⟩
  wp_apply wp_searchLeaf buf.ptr (leafHeader leafModel) leafModel _ k5 go!"zzz" (DFrac.own 1) 3 $$ [Hk5]
    as Hk5
  · iframe Hh Hb Hk5
    ipureintro
    refine ⟨Hbp, rfl, leafModel_fits, by simp [leafModel], ?_⟩
    intro i hi
    have : i < 3 := by simpa [leafModel] using hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl <;> decide +revert
  iexact HΦ

end proof

end Perennial
