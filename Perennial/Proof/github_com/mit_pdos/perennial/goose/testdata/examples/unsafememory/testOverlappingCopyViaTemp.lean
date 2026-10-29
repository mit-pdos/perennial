/-
The proof of `testOverlappingCopyViaTemp`: a `[]uint64` is the bytes of its elements; the
source `words` view is read whole before the overlapping destination view is written, so the
copy has value semantics and `buf[3]` holds the old `buf[2]`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingCopyViaTemp

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

variable [GooseExts] [go_gctx : GoGlobalContext]

/-- The elements of `buf` after `m` iterations of the loop that sets `buf[i] = i`. -/
def copyViaTemp_words (m : Nat) : List w64 :=
  (List.range 16).map (fun i => if i < m then W64 (i : Int) else 0)

theorem copyViaTemp_words_length (m : Nat) : (copyViaTemp_words m).length = 16 := by simp [copyViaTemp_words]

theorem copyViaTemp_words_set (m : Nat) :
    (copyViaTemp_words m).set m (W64 (m : Int)) = copyViaTemp_words (m + 1) := by
  apply List.ext_getElem (by simp [copyViaTemp_words])
  intro k h1 h2
  simp only [copyViaTemp_words, List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases h : m = k
  · subst h; simp
  · simp only [h, ↓reduceIte]
    by_cases h' : k < m
    · simp [h', show k < m + 1 by omega]
    · simp [h', show ¬ k < m + 1 by omega]

end github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingCopyViaTemp.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testOverlappingCopyViaTemp.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  have hlay := go.PlainLayout.scalar go.uint64 8 .isPlainScalar_uint64
  icases typedPointsto_zero_array_bytes go.uint64 hlay p_ptr _ 16 _ (by decide) (by decide) $$ p
    with ⟨%Hl, pb⟩
  have ix := fun i hi => sliceIndexRef_plain_W64 go.uint64 hlay (slice.mk p_ptr (W64 16) (W64 16))
    i Hl hi
  rw [show List.replicate 16 (zero_val w64) = copyViaTemp_words 0 from rfl]
  rename_i k_ptr
  irename : k_ptr ↦ (zero_val w64) => Hk
  ihave HI : (∃ j kv : w64,
      "i" ∷ i_ptr ↦ j ∗
      "Hk" ∷ k_ptr ↦ kv ∗
      "pb" ∷ bytesPointsto p_ptr (DFrac.own 1) ((copyViaTemp_words (sint.nat j)).flatMap encode) ∗
      "HΦ" ∷ Φ #true ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
      "buf" ∷ buf_ptr ↦ slice.mk p_ptr (W64 16) (W64 16) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 16⌝ : IProp GF) $$ [i Hk pb HΦ «$res0» buf]
  · iexists (W64 0), _
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hj : sint.Z j < 16 := by rw [show sint.Z (W64 16) = 16 from rfl] at Hif; exact Hif
    have hjn : sint.nat j < 16 := by show (sint.Z j).toNat < 16; omega
    icases bytesPointsto_view_at (V := w64) p_ptr _ _ (sint.nat j * 8)
      (sliceIndexRef w64 (sint.Z j) (slice.mk p_ptr (W64 16) (W64 16)))
      (sliceIndexRef_plain go.uint64 hlay _ j Hl Hj.1)
      (by rw [flatMap_encode_length, copyViaTemp_words_length]; omega) Hl $$ pb with ⟨Hb, pb⟩
    have hc : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (W64 16) := ⟨Hj.1, Hif⟩
    simp only [hc, and_self, ↓reduceIte]
    wp_auto
    simp only [hc, and_self, ↓reduceIte]
    wp_auto
    ispecialize pb $$ Hb
    wp_for_post
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      omega
    have hjw : W64 ((sint.nat j : Nat) : Int) = j := by
      simp only [sint.nat, Int.toNat_of_nonneg Hj.1, sint.Z, W64, BitVec.ofInt_toInt]
    have e := copyViaTemp_words_set (sint.nat j)
    rw [hjw, ← hj1] at e
    rw [replaceBytes_flatMap_set _ _ _ (by rw [copyViaTemp_words_length]; omega), e]
    iexists (j + W64 1), j
    iframe
    ipureintro
    constructor <;> word
  · have h16 : sint.nat j = 16 := by
      rw [show sint.Z (W64 16) = 16 from rfl] at Hif
      show (sint.Z j).toNat = 16; omega
    rw [h16]
    have hlen : ((copyViaTemp_words 16).flatMap encode).length = 128 := by
      rw [flatMap_encode_length, copyViaTemp_words_length]
    icases bytesPointsto_view_read (V := words) p_ptr _ _ 0 _ (ix 0 (by decide)) (by omega) Hl
      $$ pb with ⟨Hsrc, pb⟩
    unsafememory_steps
    ispecialize pb $$ Hsrc
    icases bytesPointsto_view_at (V := words) p_ptr _ _ 8 _ (ix 1 (by decide)) (by omega) Hl
      $$ pb with ⟨Hdst, pb⟩
    wp_auto
    ispecialize pb $$ Hdst
    rw [ByteEncoding.encode_decode _ (by simp only [List.length_take, List.length_drop, hlen]; rfl)]
    icases bytesPointsto_view_read (V := w64) p_ptr _ _ 24 _ (ix 3 (by decide))
      (by rw [replaceBytes_length _ _ _ (by simp [hlen])]; omega) Hl $$ pb with ⟨Hb, pb⟩
    -- the copy has value semantics: `buf[3]` is the old `buf[2]`
    have h3 : ((replaceBytes ((copyViaTemp_words 16).flatMap encode) 8
        (List.take 64 (List.drop 0 ((copyViaTemp_words 16).flatMap encode)))).drop 24).take 8 =
        (((copyViaTemp_words 16).flatMap encode).drop (2 * 8)).take 8 := by
      simp [replaceBytes, List.drop_append, List.take_append, hlen, List.drop_take, List.take_take]
    rw [h3, flatMap_encode_take_drop _ _ (by simp [copyViaTemp_words])]
    simp only [ByteEncoding.decode_encode]
    wp_auto
    iexact HΦ

end proof

end Perennial
