/-
The proof of `testFreelistOverflow`: 65536 ids, set by a loop (invariant: the ids are
`overflowIds i`), written by `writeIds` with the count in the first id and read back by `readIds`
(`Freelist.lean`); the ids stay symbolic, so nothing is computed over the 65536 elements.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistOverflow
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Freelist

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE
open github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

namespace github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory

variable [GooseExts]

/-- The elements of `ids` after `m` iterations of the loop that sets `ids[i] = i + 2`. -/
def overflowIds (m : Nat) : List w64 :=
  (List.range 65536).map (fun j => if j < m then W64 ((j : Int) + 2) else 0)

theorem overflowIds_length (m : Nat) : (overflowIds m).length = 65536 := by
  rw [overflowIds, List.length_map, List.length_range]

theorem overflowIds_zero : List.replicate 65536 (zero_val w64) = overflowIds 0 := by
  apply List.ext_getElem (by rw [List.length_replicate, overflowIds_length])
  intro k _ _
  simp only [List.getElem_replicate, overflowIds, List.getElem_map,
    Nat.not_lt_zero, ↓reduceIte]
  rfl

theorem overflowIds_set (m : Nat) :
    (overflowIds m).set m (W64 ((m : Int) + 2)) = overflowIds (m + 1) := by
  apply List.ext_getElem (by rw [List.length_set, overflowIds_length, overflowIds_length])
  intro k h1 h2
  simp only [overflowIds, List.getElem_set, List.getElem_map, List.getElem_range]
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

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistOverflow.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistOverflow.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_slice_make2 (V := w64) (W64 65536) $$ [] as %ids ⟨Hids, Hcap1⟩
  · ipureintro; decide
  rw [overflowIds_zero]
  ihave %Hilen := ownSlice_len _ _ _ $$ Hids
  have hil : ids.len = W64 65536 := by
    have h := Hilen.1; rw [overflowIds_length] at h
    have h2 : sint.Z ids.len = 65536 := by
      have : (sint.Z ids.len).toNat = 65536 := h.symm
      omega
    have e : W64 (sint.Z ids.len) = ids.len := by simp only [sint.Z, W64, BitVec.ofInt_toInt]
    rw [← e, h2]
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave HI : iprop(∃ (n kv : w64),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "Hids" ∷ ids ↦* overflowIds (sint.nat n) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 65536⌝) $$ [i k Hids]
  · iexists _, _
    rw [show sint.nat (W64 0) = 0 from rfl]
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · rw [hil, show sint.Z (W64 65536) = 65536 from rfl] at Hif
    have Hlt : sint.nat n < 65536 := by show (sint.Z n).toNat < 65536; omega
    have hc : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ids.len := ⟨Hn.1, by rw [hil]; exact Hif⟩
    rw [ite_eq_left hc]
    obtain ⟨x, Hx⟩ : ∃ x, (overflowIds (sint.nat n))[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem (by rw [overflowIds_length]; exact Hlt)⟩
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ x Hn.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hx
    rw [ite_eq_left hc]
    wp_apply wp_store_slice_index ids (sint.Z n) _ (n + W64 2) $$ [Hids] as Hids
    · iframe; ipureintro; rw [overflowIds_length]; omega
    wp_for_post
    have hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by
      show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
      have : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      omega
    have hv : n + W64 2 = W64 ((sint.nat n : Nat) + 2 : Int) := by
      have : ((sint.nat n : Nat) : Int) = sint.Z n := by
        show ((sint.Z n).toNat : Int) = sint.Z n; omega
      rw [this]; word
    rw [show (sint.Z n).toNat = sint.nat n from rfl, hv, overflowIds_set, ← hn1]
    iframe
    iexists (n + W64 1), n
    iframe
    ipureintro
    constructor <;> word
  have hn : sint.nat n = 65536 := by
    rw [hil, show sint.Z (W64 65536) = 65536 from rfl] at Hif
    show (sint.Z n).toNat = 65536; omega
  rw [hn]
  have hL := overflowIds_length 65536
  wp_func_call
  wp_call
  wp_auto
  iclear «$res0»
  rename_i res_ptr
  irename : (res_ptr ↦ zero_val Bool : IProp GF) => «$res0»
  rw [show W64 16 + W64 8 * (W64 65536 + W64 1) = W64 524312 from rfl]
  wp_apply wp_slice_make2 (V := w8) (W64 524312) $$ [] as %buf ⟨Hbuf, Hcap2⟩
  · ipureintro; decide
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  icases ownSlice_ptr_pos buf _ _
    (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf with %Hpos
  ihave Hb := ownSlice_to_bytes go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
  rw [flatMap_encode_w8]
  wp_apply wp_pageAt buf
    (by have h := Hblen.1; rw [List.length_replicate] at h
        have : (sint.Z buf.len).toNat = 524312 := h.symm
        omega)
  wp_apply wp_writeIds buf.ptr (List.replicate 524312 (zero_val w8)) ids (overflowIds 65536)
    (DFrac.own 1) (by rw [freelistIds_length, hL, List.length_replicate]; decide) (by rw [hL]; decide) $$ [Hb Hids]
    as ⟨Hb, Hids⟩
  · iframe
  unfold freelistBytes
  wp_apply wp_readIds buf.ptr
    (freelistHeader (decode (List.take 16 (List.replicate 524312 (zero_val w8)))) (overflowIds 65536))
    (overflowIds 65536) _ (by simp only [freelistHeader]) (by rw [hL]; decide) $$ [Hb] as %out ⟨Hb, %Hnil, Hout⟩
  · iframe
  ihave %Holen := ownSlice_len _ _ _ $$ Hout
  have hol : out.len = W64 65536 := by
    have h := Holen.1; rw [hL] at h
    have h2 : sint.Z out.len = 65536 := by
      have : (sint.Z out.len).toNat = 65536 := h.symm
      omega
    have e : W64 (sint.Z out.len) = out.len := by simp only [sint.Z, W64, BitVec.ofInt_toInt]
    rw [← e, h2]
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hb, Hr⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hx⟩
  icases (typedPointsto_bytes buf.ptr _ _ Hpos).2 $$ Hh with Hh
  have hcount : (freelistHeader (decode (List.take 16 (List.replicate 524312 (zero_val w8))))
      (overflowIds 65536)).count' = W16 65535 := by
    simp only [freelistHeader, freelistCount, hL]; rfl
  iclear Hr Hx Hcap1 Hcap2
  generalize freelistHeader (decode (List.take 16 (List.replicate 524312 (zero_val w8))))
    (overflowIds 65536) = H at hcount
  clear Hblen Hnil Hilen Holen
  wp_auto
  rw [hcount]
  wp_auto
  rw [hol]
  wp_auto
  iclear Hh
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave HI : iprop(∃ (m kv : w64),
      "i" ∷ i_ptr ↦ m ∗
      "k" ∷ k_ptr ↦ kv ∗
      "%Hm" ∷ ⌜0 ≤ sint.Z m ∧ sint.Z m ≤ 65536⌝) $$ [i k]
  · iexists _, _
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · rw [hil, show sint.Z (W64 65536) = 65536 from rfl] at Hif
    have Hlt : (sint.Z m).toNat < (overflowIds 65536).length := by rw [hL]; omega
    obtain ⟨x, Hx⟩ : ∃ x, (overflowIds 65536)[(sint.Z m).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hc : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z ids.len := ⟨Hm.1, by rw [hil]; exact Hif⟩
    have hc' : 0 ≤ sint.Z m ∧ sint.Z m < sint.Z out.len := ⟨Hm.1, by rw [hol]; exact Hif⟩
    rw [ite_eq_left hc]
    wp_apply wp_load_slice_index _ (sint.Z m) _ _ x Hm.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hx
    rw [ite_eq_left hc']
    wp_apply wp_load_slice_index _ (sint.Z m) _ _ x Hm.1 $$ [Hout] as Hout
    · iframe; ipureintro; exact Hx
    rw [ite_eq_left hc]
    wp_apply wp_load_slice_index _ (sint.Z m) _ _ x Hm.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hx
    wp_for_post
    iframe
    iexists (m + W64 1), m
    iframe
    ipureintro
    constructor <;> word
  iexact HΦ

end proof

end Perennial
