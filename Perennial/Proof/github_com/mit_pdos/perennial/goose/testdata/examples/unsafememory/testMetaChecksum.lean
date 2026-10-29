/-
The proof of `testMetaChecksum`: `m.write(p)` leaves a valid copy of `m` in the meta page; a
copy of that is valid too; flipping a byte of the page's `pageSize` invalidates the page's meta
(`Meta.set_checksum_ne`) but not the copy. The `Meta`s are allocated with `Meta.wp_alloc_pos`
(their byte views need positive addresses), so the steps before the allocation of `cp` are taken
with `wp_pures` and `wp_load` (`wp_auto` would allocate it).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__meta
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta__write
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta__validate

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum
variable [GooseExts]

/-- The test's `Meta`, `m` before `m.write(p)`. -/
def meta0 : Meta :=
  ⟨W32 3977042669, W32 2, W32 4096, 0, ⟨W64 3, 0⟩, W64 2, W64 4, W64 7, 0⟩

/-- `meta0` with its checksum set, as `write` leaves it in `m` and in the page. -/
def meta1 : Meta := { meta0 with checksum' := metaSum meta0 }

theorem metaSum_meta1 : metaSum meta1 = metaSum meta0 := metaSum_with_checksum _ _

theorem meta1_valid :
    decide (meta1.magic' = W32 3977042669 ∧ meta1.version' = W32 2 ∧
      meta1.checksum' = metaSum meta1) = true :=
  decide_eq_true ⟨rfl, rfl, metaSum_meta1.symm⟩

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum

open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum.wp_proof
    (wp_pageAt : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.spec (GF := GF) (hG := hG))
    (wp_meta : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.«meta».spec (GF := GF) (hG := hG))
    (wp_write : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.write.spec (GF := GF) (hG := hG))
    (wp_validate : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.validate.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testMetaChecksum.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_pures
  wp_alloc res_ptr as Hres
  wp_pures
  wp_apply +noauto Meta.wp_alloc_pos as %m ⟨Hm, %Hmpos⟩
  ihave Hm := typedPointsto_of_eq _ _ meta0 _ $$ [Hm]
  · iframe Hm; ipureintro; rfl
  wp_auto
  wp_apply wp_slice_make2 (V := w8) $$ [] as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  ihave %Hbl := ownSlice_len _ _ _ $$ Hbuf
  ihave %Hbp := ownSlice_ptr_pos _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hbuf
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) _ _ _ Hbp $$ Hbuf
    with ⟨Hb, Hbuf⟩
  rw [flatMap_encode_w8, show (zero_val w8 : w8) = 0 from rfl]
  rw [List.length_replicate] at Hbl
  have hbufW : buf.len = W64 (4096 : Nat) := w64_of_sint_nat _ _ Hbl.1 Hbl.2
  have hbufZ : sint.Z buf.len = 4096 := by rw [hbufW]; rfl
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbp, by decide, ?_⟩; rw [hbufZ]; decide
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hb
  simp only [List.length_replicate] at Hbd
  rw [show List.replicate 4096 (0 : w8) = List.replicate 16 0 ++ (List.replicate 64 0 ++
      List.replicate 4016 0) by rw [List.replicate_append_replicate, List.replicate_append_replicate]]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hb⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Ho, Hrest⟩
  rw [List.length_replicate, List.length_replicate, loc_add_assoc,
    show ((16 : Nat) : Int) = (16 : Int) from rfl, show ((64 : Nat) : Int) = (64 : Int) from rfl]
  have hp16 : 0 < (buf.ptr +ₗ 16).addr := by simp only [Loc.add]; omega
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) Hbp).1 $$ Hh with Hh
  icases (bytesPointsto_typed (V := Meta) _ _ _ (by simp) hp16).1 $$ Ho with Ho
  wp_apply wp_write m buf.ptr _ _ _ $$ [Hm Hh Ho] as ⟨Hm, Hh, Ho⟩
  · iframe; ipureintro; exact ⟨Hmpos, Hbp⟩
  ihave Hm := typedPointsto_of_eq _ _ meta1 _ $$ [Hm]
  · iframe Hm; ipureintro; rfl
  ihave Ho := typedPointsto_of_eq _ _ meta1 _ $$ [Ho]
  · iframe Ho; ipureintro; rfl
  wp_apply wp_meta
  · ipureintro; refine ⟨Hbp, ?_⟩; have := Hbd.2; omega
  wp_apply +noauto wp_validate (buf.ptr +ₗ 16) meta1 (DFrac.own 1) $$ [Ho] as Ho
  · iframe Ho; ipureintro; exact hp16
  rw [meta1_valid]
  repeat (wp_pures; wp_load)
  wp_pures
  wp_apply +noauto Meta.wp_alloc_pos as %cp ⟨Hcp, %Hcppos⟩
  wp_auto
  ihave Hcp := typedPointsto_of_eq _ _ meta1 _ $$ [Hcp]
  · iframe Hcp; ipureintro; rfl
  wp_apply wp_validate cp meta1 (DFrac.own 1) $$ [Hcp] as Hcp
  · iframe Hcp; ipureintro; exact Hcppos
  simp only [metaSum_meta1, decide_true, Bool.not_true]
  wp_auto
  have h24 : sint.Z (W64 16 + W64 8) = 24 := rfl
  have hix : sliceIndexRef w8 24 buf = buf.ptr +ₗ 24 := sliceIndexRef_byte buf 24 Hbp (by decide)
  have hc : (0 : Int) ≤ 24 ∧ (24 : Int) < 4096 := by decide
  simp only [h24, hbufZ, hix, hc, _root_.and_self, ite_true]
  icases (typedPointsto_bytes (buf.ptr +ₗ 16) meta1 _ hp16).1 $$ Ho with Ho
  icases bytesPointsto_view_at (V := w8) (buf.ptr +ₗ 16) _ (encode meta1) 8 (buf.ptr +ₗ 24)
    (by rw [loc_add_assoc]; rfl) (by simp) hp16 $$ Ho with ⟨Hx, Ho⟩
  wp_auto
  simp only [h24, hbufZ, hix, hc, _root_.and_self, ite_true]
  wp_auto
  ihave Ho := Ho $$ Hx
  have hx : (decode (List.take 1 (List.drop 8 (encode meta1))) : w8) =
      (encode meta1)[8]'(by simp) := by
    rw [decode_w8, List.drop_eq_getElem_cons (by simp)]; rfl
  rw [encode_w8, replaceBytes_single _ _ _ (by simp), hx]
  have hne := Meta.set_checksum_ne meta1 8 ((encode meta1)[8]'(by simp) ^^^ W8 1)
    (by decide) (w8_ne_xor_one _) metaSum_meta1.symm
  icases (bytesPointsto_typed (V := Meta) _ _ _ (by simp) hp16).1 $$ Ho with Ho
  wp_apply +noauto wp_validate (buf.ptr +ₗ 16) _ (DFrac.own 1) $$ [Ho] as Ho
  · iframe Ho; ipureintro; exact hp16
  rw [decide_eq_false (fun h => hne h.2.2)]
  wp_auto
  wp_apply wp_validate cp meta1 (DFrac.own 1) $$ [Hcp] as Hcp
  · iframe Hcp; ipureintro; exact Hcppos
  simp only [metaSum_meta1, decide_true]
  iexact HΦ

end proof

end Perennial
