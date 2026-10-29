/-
The proof of `testPageAtOffset`: a page at offset 4096 owns only its own bytes, so the first half of the buffer stays zero.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testPageAtOffset
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt
public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes
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

set_option goose.wp.extras true in
theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testPageAtOffset.wp_proof
    (wp_pageAt : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.pageAt.spec (GF := GF) (hG := hG))
    (wp_leafInodes : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.leafInodes.spec (GF := GF) (hG := hG))
    (wp_writeInodeToPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.writeInodeToPage.spec (GF := GF) (hG := hG))
    (wp_readInodeFromPage : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.readInodeFromPage.spec (GF := GF) (hG := hG))
    (wp_inodesEqual : github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.inodesEqual.spec (GF := GF) (hG := hG)) :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testPageAtOffset.spec (GF := GF) (hG := hG) := by
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
  have hbufW : buf.len = W64 (8192 : Nat) := w64_of_sint_nat _ _ Hbl.1 Hbl.2
  have hbufZ : sint.Z buf.len = 8192 := by rw [hbufW]; rfl
  ihave %Hbd := bytesPointsto_in_bounds _ _ _ (by
    intro h; have := congrArg List.length h; rw [List.length_replicate] at this
    exact absurd this (by decide)) $$ Hb
  simp only [List.length_replicate] at Hbd
  wp_apply wp_pageAt
  · ipureintro; refine ⟨Hbp, by decide, ?_⟩; rw [hbufZ]; decide
  rw [show sint.Z (W64 4096) = 4096 from rfl,
    show List.replicate 8192 (0 : w8) = List.replicate 4096 0 ++ (List.replicate 16 0 ++
      List.replicate 4080 0) by rw [List.replicate_append_replicate, List.replicate_append_replicate]]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hlow, Hb⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hb⟩
  rw [List.length_replicate, List.length_replicate, loc_add_assoc,
    show ((4096 : Nat) : Int) = (4096 : Int) from rfl]
  imod bytesPointsto_persist _ _ _ $$ Hlow with #Hlow
  have hp : 0 < (buf.ptr +ₗ 4096).addr := by simp only [Loc.add]; omega
  icases (bytesPointsto_typed (V := Page) _ _ _ (by simp) hp).1 $$ Hh with Hh
  wp_auto
  wp_apply wp_leafInodes as %s #Hin
  ihave %Hsl : ⌜sint.Z s.len = 3⌝ $$ [Hin]
  · unfold inodesOwn
    icases Hin with ⟨%xs, #Hs, #Hxs⟩
    ihave %Hl1 := BigSepL2.bigSepL2_length $$ Hxs
    ihave %Hl2 := ownSlice_len _ _ _ $$ Hs
    ipureintro
    exact sint_Z_eq_of_sint_nat _ _ (by rw [← Hl2.1, Hl1]; rfl) Hl2.2
  ihave Hh := typedPointsto_of_eq _ _ (⟨W64 1, W16 2, W16 3, 0⟩ : Page) _ $$ [Hh]
  · iframe Hh; ipureintro; rw [Hsl]; rfl
  rw [show ((16 : Nat) : Int) = (16 : Int) from rfl, ← loc_add_assoc]
  have hbody := leafModel_body_length true
  wp_apply wp_writeInodeToPage _ leafModel (buf.ptr +ₗ 4096) ⟨W64 1, W16 2, W16 3, 0⟩ 4080 $$ [Hh Hb]
    as %w ⟨Hh, Hb⟩
  · iframe Hh Hb Hin; ipureintro; exact ⟨hp, leafModel_fits, by rw [hbody]; omega⟩
  imod typedPointsto_persist_view _ _ _ hp $$ Hh with #Hh
  imod bytesPointsto_persist _ _ _ $$ Hb with #Hb
  have hlf : pageIsLeaf (⟨W64 1, W16 2, W16 3, 0⟩ : Page) = true := by
    unfold pageIsLeaf
    have : (W16 2 &&& W16 2 : w16) = W16 2 := by rfl
    rw [this]; exact decide_eq_true (by intro h; cases h)
  rw [hlf]
  ihave HI : (∃ j : w64,
      "i" ∷ i_ptr ↦ j ∗
      "HΦ" ∷ Φ #true ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
      "buf" ∷ buf_ptr ↦ buf ∗
      "«in»" ∷ in_ptr ↦ s ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 4096⌝ : IProp GF) $$ [i HΦ «$res0» buf «in»]
  · iexists (W64 0); iframe; ipureintro; decide
  wp_for HI
  have hjt : sint.Z j = j.toInt := rfl
  wp_if_destruct
  · -- buf[j] is still zero
    rw [show sint.Z (W64 4096) = 4096 from rfl] at Hif
    have hjZ : sint.Z j = (sint.nat j : Int) := by
      simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z buf.len from ⟨Hj.1, by omega⟩,
      _root_.and_self, ↓reduceIte]
    ihave Hz := bytesPointsto_sub buf.ptr (List.replicate 4096 0) [0] (sint.nat j)
      (by rw [List.length_replicate, List.length_singleton]; omega)
      (by rw [List.length_singleton, List.drop_replicate, List.take_replicate,
            Nat.min_eq_left (by omega)]; rfl) $$ Hlow
    icases (bytesPointsto_typed (V := w8) (buf.ptr +ₗ ((sint.nat j : Nat) : Int)) DFrac.discard [0]
      rfl (by simp only [Loc.add]; omega)).1 $$ Hz with Hz
    rw [sliceIndexRef_byte _ _ Hbp Hj.1, hjZ]
    wp_auto
    wp_for_post
    iexists (j + W64 1)
    iframe
    ipureintro; constructor <;> word
  · -- the page
    wp_apply wp_pageAt
    · ipureintro; refine ⟨Hbp, by decide, ?_⟩; rw [hbufZ]; decide
    rw [show sint.Z (W64 4096) = 4096 from rfl]
    icases typedPointsto_split _ _ _ $$ Hh with Hh'
    simp only [TypedPointsto.typedPointstoDef]
    icases Hh' with ⟨Hid, Hflags, Hcount, Hoverflow, -⟩
    wp_auto
    wp_apply wp_pageAt
    · ipureintro; refine ⟨Hbp, by decide, ?_⟩; rw [hbufZ]; decide
    rw [show sint.Z (W64 4096) = 4096 from rfl]
    wp_apply wp_readInodeFromPage (buf.ptr +ₗ 4096) ⟨W64 1, W16 2, W16 3, 0⟩ leafModel _ as %out #Hout
    · rw [hlf]
      iframe Hh Hb; ipureintro; exact ⟨hp, rfl, leafModel_fits⟩
    wp_apply wp_inodesEqual out s _ leafModel as -
    · iframe Hout Hin
    have hrb : readBack (pageIsLeaf (⟨W64 1, W16 2, W16 3, 0⟩ : Page)) leafModel = leafModel := by
      rw [hlf]; simp [readBack, leafModel]
    rw [hrb, decide_eq_true rfl]
    iexact HΦ

end proof

end Perennial
