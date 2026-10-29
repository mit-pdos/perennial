/-
The proof of `testAliasing`: the buffer, a value slice, an element pointer and the element array are views of the same bytes.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAliasing
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElement
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page__leafPageElements
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement__value
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes

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

/-- The header and elements and data of the leaf page of `leafModel`. -/
def aliasBytes : List w8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 101, 49, 98, 97, 110, 97, 110, 97, 50, 50, 99, 104, 101, 114, 114, 121]

/-- `aliasBytes` after `v[0] = 'X'`. -/
def aliasBytes1 : List w8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 97, 112, 112, 108, 101, 49, 98, 97, 110, 97, 110, 97, 88, 50, 99, 104, 101, 114, 114, 121]

/-- `aliasBytes1` after `elems[2].vsize = 1`. -/
def aliasBytes2 : List w8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 30, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 97, 112, 112, 108, 101, 49, 98, 97, 110, 97, 110, 97, 88, 50, 99, 104, 101, 114, 114, 121]

/-- `aliasBytes2` after `buf[52] = 0`. -/
def aliasBytes3 : List w8 :=
  [0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 48, 0, 0, 0, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 38, 0, 0, 0, 6, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 1, 0, 0, 0, 97, 112, 112, 108, 101, 49, 98, 97, 110, 97, 110, 97, 88, 50, 99, 104, 101, 114, 114, 121]

theorem aliasBytes_eq : encode (leafHeader leafModel) ++ pageBody true leafModel = aliasBytes := by
  simp [aliasBytes, encode, ByteEncoding.encode, natBytes, leafHeader, leafModel, pageBody, elemBytes,
    leafElems, dataBytes, dataOff, InodeM.kv]
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAliasing.wp_proof
    (wp_leafInodes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.spec (GF := GF) (hG := hG))
    (wp_writeLeaf : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeLeaf.spec (GF := GF) (hG := hG))
    (wp_leafPageElement : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElement.spec (GF := GF) (hG := hG))
    (wp_leafPageElements : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Page.leafPageElements.spec (GF := GF) (hG := hG))
    (wp_leafValue : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafPageElement.value.spec (GF := GF) (hG := hG))
    (wp_pageBytes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageBytes.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testAliasing.spec (GF := GF) (hG := hG) := by
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
  ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hb
  simp only [List.length_replicate] at Hbd
  wp_apply wp_leafInodes as %s #Hin
  have hbody := leafModel_body_length true
  wp_apply wp_writeLeaf buf s leafModel 4096 $$ [Hb] as Hb
  · iframe Hb Hin; ipureintro; exact ⟨hbufW, by decide, leafModel_fits, by rw [hbody]; omega⟩
  rw [aliasBytes_eq]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hc, -⟩
  have hl : 0 < buf.ptr.addr := Hbp
  -- `p.leafPageElement(1).value()`: the value "22" at 76
  wp_apply wp_leafPageElement
  · ipureintro; refine ⟨hl, ?_⟩; rw [show uint.Z (W16 1) = 1 from rfl]; omega
  rw [show uint.Z (W16 1) = 1 from rfl, show (16 : Int) + 16 * 1 = ((32 : Nat) : Int) from rfl]
  icases bytesPointsto_view_read (V := leafPageElement) buf.ptr _ aliasBytes 32 _ rfl
    (by decide) hl $$ Hc with ⟨Hel, Hc⟩
  have he1 : (decode ((aliasBytes.drop 32).take 16) : leafPageElement) = ⟨0, W32 38, W32 6, W32 2⟩ := by
    simp [aliasBytes, decode, ByteEncoding.decode, bytesNat]
  rw [he1]
  wp_apply wp_leafValue $$ [Hel] as Hel
  · iframe Hel; ipureintro; refine ⟨by simp only [Loc.add]; omega, ?_⟩
    simp only [Loc.add, show uint.Z (W32 38) = 38 from rfl, show uint.Z (W32 6) = 6 from rfl,
      show uint.Z (W32 2) = 2 from rfl]; omega
  ispecialize Hc $$ Hel
  rw [show uint.Z (W32 38) = 38 from rfl, show uint.Z (W32 6) = 6 from rfl,
    show uint.Z (W32 2) = 2 from rfl, loc_add_assoc]
  -- `v[0] = 'X'` writes byte 76 of the buffer
  simp only [show sint.Z (W64 0) = 0 from rfl, show sint.Z (W64 2) = 2 from rfl,
    show (0 : Int) ≤ 0 ∧ (0 : Int) < 2 from ⟨by decide, by decide⟩]
  rw [show sliceIndexRef w8 0 (slice.mk (buf.ptr +ₗ ((32 : Nat) + (38 + 6) : Int)) (W64 2) (W64 2)) =
    buf.ptr +ₗ ((76 : Nat) : Int) by
      rw [sliceIndexRef_byte _ _ (by simp only [Loc.add]; omega) (by decide)]; simp]
  icases bytesPointsto_view_at (V := w8) buf.ptr _ aliasBytes 76 _ rfl (by decide) hl $$ Hc
    with ⟨Hx, Hc⟩
  wp_auto
  ispecialize Hc $$ Hx
  rw [show replaceBytes aliasBytes 76 (encode (W8 88)) = aliasBytes1 by rfl]
  -- `buf[76]` and `pageBytes(p, len(buf))[76]` see it
  have hbufZ : sint.Z buf.len = 4096 := by rw [hbufW]; rfl
  simp only [hbufZ, show sint.Z (W64 76) = 76 from rfl,
    show (0 : Int) ≤ 76 ∧ (76 : Int) < 4096 from ⟨by decide, by decide⟩]
  rw [show sliceIndexRef w8 76 buf = buf.ptr +ₗ ((76 : Nat) : Int) by
      rw [sliceIndexRef_byte _ _ hl (by decide)]; rfl]
  icases bytesPointsto_view_read (V := w8) buf.ptr _ aliasBytes1 76 _ rfl (by decide) hl $$ Hc
    with ⟨Hx, Hc⟩
  rw [show (decode ((aliasBytes1.drop 76).take 1) : w8) = W8 88 by rfl]
  wp_auto
  ispecialize Hc $$ Hx
  wp_apply wp_pageBytes
  · ipureintro; rw [hbufZ]; omega
  simp only [hbufZ, show sint.Z (W64 76) = 76 from rfl,
    show (0 : Int) ≤ 76 ∧ (76 : Int) < 4096 from ⟨by decide, by decide⟩]
  rw [show sliceIndexRef w8 76 (slice.mk buf.ptr buf.len buf.len) = buf.ptr +ₗ ((76 : Nat) : Int) by
      rw [sliceIndexRef_byte (slice.mk buf.ptr buf.len buf.len) 76 hl (by decide)]; rfl]
  icases bytesPointsto_view_read (V := w8) buf.ptr _ aliasBytes1 76 _ rfl (by decide) hl $$ Hc
    with ⟨Hx, Hc⟩
  rw [show (decode ((aliasBytes1.drop 76).take 1) : w8) = W8 88 by rfl]
  wp_auto
  ispecialize Hc $$ Hx
  -- `p.leafPageElements()`
  icases bytesPointsto_view_read (V := Page) buf.ptr _ aliasBytes1 0 buf.ptr (by simp) (by decide) hl
    $$ Hc with ⟨Hpg, Hc⟩
  rw [show (decode ((aliasBytes1.drop 0).take 16) : Page) = ⟨0, W16 2, W16 3, 0⟩ by rfl]
  wp_apply wp_leafPageElements $$ [Hpg] as Hpg
  · iframe Hpg; ipureintro; refine ⟨hl, ?_⟩; rw [show uint.Z (W16 3) = 3 from rfl]; omega
  ispecialize Hc $$ Hpg
  simp only [show ¬ (W16 3 = W16 0) by intro h; exact absurd (congrArg BitVec.toNat h) (by decide),
    ↓reduceIte]
  rw [show uint.Z (W16 3) = 3 from rfl]
  -- `elems[2].vsize = 1` writes through the element array
  have h48 : sliceIndexRef leafPageElement 2 (slice.mk (buf.ptr +ₗ 16) (W64 3) (W64 3)) =
      buf.ptr +ₗ ((48 : Nat) : Int) := by
    simp only [sliceIndexRef]
    rw [arrayIndexRef_plain_eq _ leafPageElement.layout _ _ (by simp only [Loc.add]; omega)
      (by decide), loc_add_assoc]
    rfl
  simp only [show sint.Z (W64 2) = 2 from rfl,
    show sint.Z (slice.mk (buf.ptr +ₗ 16) (W64 3) (W64 3)).len = 3 from rfl,
    show (0 : Int) ≤ 2 ∧ (2 : Int) < 3 from ⟨by decide, by decide⟩, h48]
  icases bytesPointsto_view_at (V := leafPageElement) buf.ptr _ aliasBytes1 48 _ rfl (by decide) hl
    $$ Hc with ⟨Hel, Hc⟩
  rw [show (decode ((aliasBytes1.drop 48).take 16) : leafPageElement) = ⟨0, W32 30, W32 6, W32 0⟩ by
    simp [aliasBytes1, decode, ByteEncoding.decode, bytesNat]]
  wp_auto
  ispecialize Hc $$ Hel
  have hrepl : replaceBytes aliasBytes1 48 (encode (⟨0, W32 30, W32 6, W32 1⟩ : leafPageElement)) =
      aliasBytes2 := by
    simp [replaceBytes, aliasBytes1, aliasBytes2, encode, ByteEncoding.encode, natBytes]
  simp only [hrepl]
  -- `buf[52] = 0` writes the third element's pos
  simp only [hbufZ, show sint.Z (W64 52) = 52 from rfl,
    show (0 : Int) ≤ 52 ∧ (52 : Int) < 4096 from ⟨by decide, by decide⟩]
  rw [show sliceIndexRef w8 52 buf = buf.ptr +ₗ ((52 : Nat) : Int) by
      rw [sliceIndexRef_byte _ _ hl (by decide)]; rfl]
  icases bytesPointsto_view_at (V := w8) buf.ptr _ aliasBytes2 52 _ rfl (by decide) hl $$ Hc
    with ⟨Hx, Hc⟩
  wp_auto
  ispecialize Hc $$ Hx
  rw [show replaceBytes aliasBytes2 52 (encode (W8 0)) = aliasBytes3 by rfl]
  -- `p.leafPageElement(2)` and `elems[2]` see both writes
  wp_apply wp_leafPageElement
  · ipureintro; refine ⟨hl, ?_⟩; rw [show uint.Z (W16 2) = 2 from rfl]; omega
  rw [show uint.Z (W16 2) = 2 from rfl, show (16 : Int) + 16 * 2 = ((48 : Nat) : Int) from rfl]
  icases bytesPointsto_view_read (V := leafPageElement) buf.ptr _ aliasBytes3 48 _ rfl (by decide) hl
    $$ Hc with ⟨Hel, Hc⟩
  rw [show (decode ((aliasBytes3.drop 48).take 16) : leafPageElement) = ⟨0, W32 0, W32 6, W32 1⟩ by
    simp [aliasBytes3, decode, ByteEncoding.decode, bytesNat]]
  wp_auto
  simp only [show sint.Z (W64 2) = 2 from rfl, h48]
  wp_auto
  ispecialize Hc $$ Hel
  wp_apply wp_pageBytes
  · ipureintro; rw [hbufZ]; omega
  iexact HΦ

end proof

end Perennial
