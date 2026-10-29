/-
The proof of `testBufferReuseShifted`: an `InBucket` load at offset 0, a loop zeroing the
bytes (invariant: a prefix of zeros), then an `InBucket` stored and loaded at offset 8 through
byte views of the buffer.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBufferReuseShifted

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBufferReuseShifted.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testBufferReuseShifted.spec (GF := GF) (hG := hG) := by
  unsafememory_auto
  icases typedPointsto_zero_byte_array p_ptr _ 32 _ (by decide) (by decide) $$ p with ⟨%Hl, p⟩
  have ix := fun i hi => sliceIndexRef_byte_W64 (slice.mk p_ptr (W64 32) (W64 32)) i Hl hi
  icases bytesPointsto_view_at (V := w8) p_ptr _ _ 0 _ (ix 0 (by decide)) (by simp) Hl $$ p
    with ⟨Hb, p⟩
  wp_pures
  wp_store
  ispecialize p $$ Hb
  icases bytesPointsto_view_read (V := InBucket) p_ptr _ _ 0 _ (ix 0 (by decide))
    (by simp [replaceBytes, encode_w8]) Hl $$ p with ⟨Hx, p⟩
  wp_auto
  ispecialize p $$ Hx
  rename_i k_ptr
  irename : k_ptr ↦ (zero_val w64) => Hk
  ihave HI : (∃ j kv : w64,
      "i" ∷ i_ptr ↦ j ∗
      "Hk" ∷ k_ptr ↦ kv ∗
      "p" ∷ bytesPointsto p_ptr (DFrac.own 1) ((List.replicate 32 0).take (sint.nat j) ++
        (replaceBytes (List.replicate 32 0) 0 (encode (W8 1))).drop (sint.nat j)) ∗
      "HΦ" ∷ Φ #true ∗
      "«$res0»" ∷ «$res0_ptr» ↦ zero_val Bool ∗
      "buf" ∷ buf_ptr ↦ slice.mk p_ptr (W64 32) (W64 32) ∗
      "old" ∷ old_ptr ↦ (decode (List.take 16 (List.drop 0 (replaceBytes (List.replicate 32 0) 0
        (encode (W8 1))))) : InBucket) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 32⌝ : IProp GF) $$ [i Hk p HΦ «$res0» buf old]
  · iexists (W64 0), _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero, List.nil_append]
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have hj : sint.Z j < 32 := by rw [show sint.Z (W64 32) = 32 from rfl] at Hif; exact Hif
    have hjn : sint.nat j < 32 := by show (sint.Z j).toNat < 32; omega
    icases bytesPointsto_view_at (V := w8) p_ptr _ _ (sint.nat j)
      (sliceIndexRef w8 (sint.Z j) (slice.mk p_ptr (W64 32) (W64 32)))
      (by rw [sliceIndexRef_byte _ _ Hl Hj.1]; simp only [sint.nat, Int.toNat_of_nonneg Hj.1])
      (by simp [replaceBytes, encode_w8]; omega) Hl $$ p with ⟨Hb, p⟩
    have hc : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z (W64 32) := ⟨Hj.1, Hif⟩
    simp only [hc, and_self, ↓reduceIte]
    wp_auto
    simp only [hc, and_self, ↓reduceIte]
    wp_auto
    ispecialize p $$ Hb
    wp_for_post
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      omega
    have e : replaceBytes (List.take (sint.nat j) (List.replicate 32 0) ++
        List.drop (sint.nat j) (replaceBytes (List.replicate 32 0) 0 (encode (W8 1))))
        (sint.nat j) (encode (W8 0)) =
        List.take (sint.nat (j + W64 1)) (List.replicate 32 0) ++
        List.drop (sint.nat (j + W64 1)) (replaceBytes (List.replicate 32 0) 0 (encode (W8 1))) := by
      have key : ∀ B : List w8, B.length = 32 →
          replaceBytes (List.take (sint.nat j) (List.replicate 32 0) ++ List.drop (sint.nat j) B)
            (sint.nat j) (encode (W8 0)) =
          List.take (sint.nat j + 1) (List.replicate 32 0) ++ List.drop (sint.nat j + 1) B := by
        intro B hB
        rw [encode_w8, replaceBytes_single _ _ _ (by simp; omega)]
        exact list_copy_step B (List.replicate 32 0) (sint.nat j) (W8 0) (by omega)
          (by rw [List.getElem?_replicate]; simp [hjn])
      rw [hj1]
      exact key _ (by simp [replaceBytes, encode_w8])
    rw [e]
    iexists (j + W64 1), j
    iframe
    ipureintro
    constructor <;> word
  · have h32 : sint.nat j = 32 := by
      rw [show sint.Z (W64 32) = 32 from rfl] at Hif
      show (sint.Z j).toNat = 32; omega
    rw [h32, show List.drop 32 (replaceBytes (List.replicate 32 0) 0 (encode (W8 1))) = [] by
      simp [replaceBytes, encode_w8], List.append_nil, List.take_of_length_le (by simp)]
    icases bytesPointsto_view_at (V := InBucket) p_ptr _ _ 8 _ (ix 8 (by decide)) (by simp) Hl $$ p
      with ⟨Hv, p⟩
    wp_auto
    ispecialize p $$ Hv
    icases bytesPointsto_view_read (V := w8) p_ptr _ _ 0 _ (ix 0 (by decide))
      (by simp [replaceBytes, encode]) Hl $$ p with ⟨Hb, p⟩
    wp_auto
    iexact HΦ

end proof

end Perennial
