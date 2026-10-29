/-
The proof of `testFreelistRoundTrip`: three ids written over a 40-byte page by `writeIds` and read
back by `readIds` (`Freelist.lean`), then an empty page, whose ids read back as `nil`.
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistRoundTrip
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.Freelist

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

-- `wp_slice_literal` expects the slice literal folded, which this pure step would unfold.
attribute [-instance] go.SliceSemantics.composite_literal_slice

theorem github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistRoundTrip.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.unsafememory.testFreelistRoundTrip.spec (GF := GF) (hG := hG) := by
  intro Φ
  iintro HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_slice_literal (V := Pgid)
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hids, Hcap1⟩
  rw [show go.arrayLiteralSize [KeyedElement none (ElementExpression Pgid.ty #(W64 5)),
    KeyedElement none (ElementExpression Pgid.ty #(W64 3)),
    KeyedElement none (ElementExpression Pgid.ty #(W64 9))] = 3 from rfl,
    show sint.nat (W64 (0 + 1)) = 1 from rfl, show sint.nat (W64 (0 + 1 + 1)) = 2 from rfl]
  simp only [List.set_cons_succ, List.set_cons_zero]
  wp_auto
  wp_func_call
  wp_call
  wp_auto
  rw [show W64 16 + W64 8 * W64 3 = W64 40 from rfl]
  wp_apply wp_slice_make2 (V := w8) (W64 40) $$ [] as %buf ⟨Hbuf, Hcap2⟩
  · ipureintro; decide
  ihave %Hblen := ownSlice_len _ _ _ $$ Hbuf
  icases ownSlice_ptr_pos buf _ _ (by simp) $$ Hbuf with %Hpos
  ihave Hb := ownSlice_to_bytes go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
  rw [flatMap_encode_w8]
  wp_apply wp_pageAt_zero buf
    (by have h := Hblen.1; rw [List.length_replicate] at h
        have : (sint.Z buf.len).toNat = 40 := h.symm
        omega)
  wp_apply wp_writeIds buf.ptr (List.replicate 40 (zero_val w8)) (slice.mk sl (W64 3) (W64 3)) [W64 5, W64 3, W64 9] (DFrac.own 1)
    (by simp [freelistIds]) (by simp) $$ [Hb Hids] as ⟨Hb, Hids⟩
  · iframe
  unfold freelistBytes
  wp_apply wp_readIds buf.ptr
    (freelistHeader (decode (List.take 16 (List.replicate 40 (zero_val w8)))) [W64 5, W64 3, W64 9])
    [W64 5, W64 3, W64 9] _ rfl (by simp) $$ [Hb] as %out ⟨Hb, %Hnil, Hout⟩
  · iframe
  ihave %Holen := ownSlice_len _ _ _ $$ Hout
  have hol : out.len = W64 3 := by
    have h := Holen.1; simp only [List.length_cons, List.length_nil] at h
    have : (sint.Z out.len).toNat = 3 := h.symm
    word
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hb, Hr⟩
  icases (bytesPointsto_app _ _ _ _).1 $$ Hb with ⟨Hh, Hx⟩
  icases (typedPointsto_bytes buf.ptr _ _ Hpos).2 $$ Hh with Hh
  wp_auto
  rw [hol]
  wp_auto
  iclear Hr Hx Hh «$res0» Hcap1 Hcap2
  rename_i res_ptr k_ptr
  irename : (res_ptr ↦ zero_val Bool : IProp GF) => «$res0»
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave HI : iprop(∃ (n kv : w64),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ 3⌝) $$ [i k]
  · iexists _, _
    iframe
    ipureintro; decide
  wp_for HI
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < 3 := by
      rw [show sint.Z (W64 3) = 3 from rfl] at Hif; omega
    obtain ⟨x, Hx⟩ : ∃ x, [W64 5, W64 3, W64 9][(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) from ⟨Hn.1, Hif⟩]
    simp only [and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ x Hn.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hx
    rw [hol]
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) from ⟨Hn.1, Hif⟩, and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ x Hn.1 $$ [Hout] as Hout
    · iframe; ipureintro; exact Hx
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z (W64 3) from ⟨Hn.1, Hif⟩, and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index _ (sint.Z n) _ _ x Hn.1 $$ [Hids] as Hids
    · iframe; ipureintro; exact Hx
    wp_for_post
    iframe
    iexists (n + W64 1), n
    iframe
    ipureintro
    rw [show sint.Z (W64 3) = 3 from rfl] at Hif
    constructor <;> word
  iclear Hids Hout
  wp_func_call
  wp_call
  wp_auto
  iclear «$res0»
  rw [show W64 16 + W64 8 * W64 0 = W64 16 from rfl]
  wp_apply wp_slice_make2 (V := w8) (W64 16) $$ [] as %emp ⟨Hemp, _⟩
  · ipureintro; decide
  ihave %Helen := ownSlice_len _ _ _ $$ Hemp
  icases ownSlice_ptr_pos emp _ _ (by simp) $$ Hemp with %Hepos
  ihave He := ownSlice_to_bytes go.uint8 (.scalar _ _ .isPlainScalar_uint8) emp _ _ Hepos $$ Hemp
  rw [flatMap_encode_w8]
  have helen : 0 < sint.Z emp.len := by
    have h := Helen.1; rw [List.length_replicate] at h
    have : (sint.Z emp.len).toNat = 16 := h.symm
    omega
  wp_apply wp_pageAt_zero emp helen
  ihave Hnil := ownSlice_nil (V := w64) (DFrac.own 1)
  wp_apply wp_writeIds emp.ptr (List.replicate 16 (zero_val w8)) slice.nil [] (DFrac.own 1)
    (by simp [freelistIds]) (by simp) $$ [He] as ⟨He, _⟩
  · iframe; iexact Hnil
  wp_apply wp_pageAt_zero emp helen
  unfold freelistBytes
  wp_apply wp_readIds emp.ptr
    (freelistHeader (decode (List.take 16 (List.replicate 16 (zero_val w8)))) []) [] _ rfl (by simp)
    $$ [He] as %s ⟨_, %Hs, _⟩
  · iframe
  rw [Hs rfl]
  wp_auto
  iexact HΦ

end proof

end Perennial
