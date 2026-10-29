/-
The proof of `(*Meta).sum64`: the loop is FNV-1a over the 56 bytes before the checksum.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta__sum64

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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.sum64.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Meta.sum64.spec (GF := GF) (hG := hG) := by
  intro m v dq
  wp_start as ⟨Hm, %Hpos⟩
  icases (typedPointsto_bytes m v dq Hpos).1 $$ Hm with Hm
  have hlen : (encode v).length = 64 := ByteEncoding.encode_length v
  rw [← List.take_append_drop 56 (encode v)]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hm with ⟨Ha, Hb⟩
  have h56 : ((encode v).take 56).length = 56 := by simp [hlen]
  icases (bytesPointsto_ownSlice m dq _ Hpos (by omega)).1 $$ Ha with Ha
  rw [h56]
  wp_auto
  rw [show arrayIndexRef w8 (sint.Z (W64 0)) m = m from go.arrayIndexRef_0 _ _,
    show (W64 56 - W64 0 : w64) = W64 56 from rfl]
  rw [show ((56 : Nat) : Int) = 56 from rfl]
  generalize hbs : (encode v).take 56 = bs at h56
  ihave HI : (∃ (j : w64) (cv : w8),
      "i" ∷ i_ptr ↦ j ∗
      "c" ∷ c_ptr ↦ cv ∗
      "h" ∷ h_ptr ↦ fnvFrom fnvOffset (bs.take (sint.nat j)) ∗
      "Ha" ∷ slice.mk m (W64 56) (W64 56) ↦*{dq} bs ∗
      "HΦ" ∷ (m ↦{dq} v -∗ Φ #(metaSum v)) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ Perennial.zero_val w64 ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 56⌝ : IProp GF) $$ [i c h Ha HΦ «$res0»]
  · iexists (W64 0), _
    iframe
    ipureintro; decide
  wp_for HI
  have hjt : sint.Z j = j.toInt := rfl
  wp_if_destruct
  · rw [show sint.Z (W64 56) = 56 from rfl] at Hif
    have hjZ : sint.Z j = (sint.nat j : Int) := by
      simp only [sint.nat]; rw [Int.toNat_of_nonneg Hj.1]
    have hjn : sint.nat j < bs.length := by omega
    simp only [show sint.Z (W64 56) = 56 from rfl,
      show 0 ≤ sint.Z j ∧ sint.Z j < 56 from ⟨Hj.1, by omega⟩, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z j) bs dq bs[sint.nat j] Hj.1 $$ [Ha] as Ha
    · iframe Ha
      ipureintro; exact List.getElem?_eq_getElem hjn
    wp_for_post
    have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      omega
    have hc : (W64 (uint.Z bs[sint.nat j]) : w64) = bs[sint.nat j].setWidth 64 := by
      apply BitVec.eq_of_toNat_eq
      have := bs[sint.nat j].isLt
      simp only [uint.Z, W64, BitVec.toNat_setWidth, BitVec.toNat_ofInt]
      omega
    have hstep : fnvFrom fnvOffset (bs.take (sint.nat j + 1)) =
        (fnvFrom fnvOffset (bs.take (sint.nat j)) ^^^ W64 (uint.Z bs[sint.nat j])) *
          W64 1099511628211 := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjn, hc]
      simp only [fnvFrom, List.foldl_append, Option.toList_some, List.foldl_cons, List.foldl_nil]
      rfl
    iframe Hb
    iexists (j + W64 1), bs[sint.nat j]
    rw [hj1, hstep]
    iframe
    ipureintro; constructor <;> word
  · have hj : sint.nat j = 56 := by
      rw [show sint.Z (W64 56) = 56 from rfl] at Hif; simp only [sint.nat]; omega
    rw [hj, ← h56, List.take_length]
    icases (bytesPointsto_ownSlice m dq bs Hpos (by omega)).2 $$ [Ha] with Ha
    · rw [h56]; iexact Ha
    rw [← hbs]
    ihave Hm := (bytesPointsto_app m dq ((encode v).take 56) ((encode v).drop 56)).2 $$ [Ha Hb]
    · rw [show ((encode v).take 56).length = 56 by simp [hlen]]; iframe
    rw [List.take_append_drop]
    ihave Hm := (typedPointsto_bytes m v dq Hpos).2 $$ Hm
    rw [show fnvFrom fnvOffset ((encode v).take 56) = metaSum v from rfl]
    iapply HΦ $$ Hm

end proof

end Perennial
