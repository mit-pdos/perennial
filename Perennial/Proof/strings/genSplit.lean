/-
The proof of `strings.genSplit`.
-/
module

public import Perennial.Spec.strings.genSplit
public import Perennial.Spec.strings.Count
public import Perennial.Spec.strings.Index
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

theorem strings.genSplit.wp_proof
    (wp_Count : strings.Count.spec (GF := GF) (hG := hG))
    (wp_Index : strings.Index'.spec (GF := GF) (hG := hG)) :
    strings.genSplit.spec (GF := GF) (hG := hG) := fun s sep Hsep Hs => by
  wp_start
  wp_auto
  rw [decide_eq_false Hsep]
  wp_auto
  have Hc := countOcc_le s sep Hsep
  wp_apply wp_Count s sep Hsep (by omega)
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  rw [decide_eq_false (show ¬ sint.Z (W64 s.length + W64 1) <
    sint.Z (W64 (countOcc s sep) + W64 1) by word)]
  wp_auto
  wp_apply wp_slice_make2 (V := GoString) (W64 (countOcc s sep) + W64 1) as %a ⟨Ha, Hacap⟩
  · ipureintro; word
  rw [show sint.nat (W64 (countOcc s sep) + W64 1) = countOcc s sep + 1 by word,
    show (zero_val GoString) = ([] : GoString) from rfl]
  ihave %Halen := ownSlice_len $$ Ha
  simp only [List.length_replicate] at Halen
  ihave IH : iprop(∃ (i : w64) (cur : GoString) (fields : List GoString),
      "i" ∷ i_ptr ↦ i ∗
      "s" ∷ s_ptr ↦ cur ∗
      "Ha" ∷ a ↦* (fields ++ List.replicate (countOcc s sep + 1 - fields.length) ([] : GoString)) ∗
      "%Hinv" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i = fields.length ∧ fields.length ≤ countOcc s sep ∧
        split s sep = fields ++ split cur sep ∧
        countOcc cur sep = countOcc s sep - fields.length ∧ cur.length ≤ s.length⌝) $$ [i s Ha]
  · iexists (W64 0), s, []
    iframe
    ipureintro
    exact ⟨by decide, rfl, by simp, by simp, by simp, Nat.le_refl _⟩
  wp_for IH
  obtain ⟨Hi0, Hi, Hfl, Hsplit, Hcnt, Hcur⟩ := Hinv
  wp_if_destruct
  · -- a field before the next occurrence of `sep`
    wp_apply wp_Index
    rcases internal.bytealg.indexResult_cases cur sep with ⟨j, hj, hres, hjle⟩ | ⟨hj, hres⟩
    · have Hend := firstOcc_end_le cur sep j hj
      rw [hres, decide_eq_false (show ¬ sint.Z (W64 j) < sint.Z (W64 0) by word)]
      wp_auto
      rw [ite_eq_left ⟨by word, by word, by word⟩,
        show sint.nat (W64 j + W64 0) - 0 = j by word, List.drop_zero]
      wp_auto
      ihave %Halen' := ownSlice_len $$ Ha
      simp only [List.length_append, List.length_replicate] at Halen'
      rw [ite_eq_left ⟨by word, by word⟩]
      wp_apply wp_store_slice_index (V := GoString) a (sint.Z i) _ (cur.take j) $$ [Ha] as Ha
      · iframe; ipureintro; simp only [List.length_append, List.length_replicate]; word
      wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hcurl
      rw [ite_eq_left ⟨by word, by word, by word⟩,
        show sint.nat (W64 j + W64 sep.length) = j + sep.length by word,
        show (cur.drop (j + sep.length)).take (sint.nat (W64 cur.length) - (j + sep.length)) =
          cur.drop (j + sep.length) from List.take_of_length_le (by rw [List.length_drop]; word)]
      wp_auto
      wp_for_post
      iframe
      iexists _, _, fields ++ [cur.take j]
      have Hset :
          (fields ++ List.replicate (countOcc s sep + 1 - fields.length) ([] : GoString)).set
          (sint.Z i).toNat (cur.take j) =
          (fields ++ [cur.take j]) ++
            List.replicate (countOcc s sep + 1 - (fields ++ [cur.take j]).length) [] := by
        rw [show (sint.Z i).toNat = fields.length by word,
          List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
        obtain ⟨m', hm'⟩ : ∃ m', countOcc s sep + 1 - fields.length = m' + 1 :=
          ⟨countOcc s sep - fields.length, by omega⟩
        rw [hm', List.replicate_succ, List.set_cons_zero, List.length_append,
          List.length_singleton, show countOcc s sep + 1 - (fields.length + 1) = m' by omega]
        simp
      rw [Hset]
      iframe
      ipureintro
      rw [countOcc_some cur sep Hsep j hj] at Hcnt
      refine ⟨by word, by simp; word, by simp; omega, ?_, by simp; omega, by simp; omega⟩
      rw [Hsplit, split_some cur sep Hsep j hj]
      simp
    · rw [countOcc_none cur sep Hsep hj] at Hcnt
      have := Hif
      exfalso; word
  · -- the last field: `a[i] = s`, return `a[:i+1]`
    have Hic : fields.length = countOcc s sep := by word
    rw [Hic, Nat.sub_self] at Hcnt
    have Hnone : internal.bytealg.firstOcc cur sep = none := by
      rcases h : internal.bytealg.firstOcc cur sep with _ | k
      · rfl
      · rw [countOcc_some cur sep Hsep k h] at Hcnt; omega
    ihave %Halen' := ownSlice_len $$ Ha
    ihave %Hawf := ownSlice_wf $$ Ha
    simp only [List.length_append, List.length_replicate] at Halen'
    rw [ite_eq_left ⟨Hi0, by word⟩]
    wp_apply wp_store_slice_index (V := GoString) a (sint.Z i) _ cur $$ [Ha] as Ha
    · iframe; ipureintro; simp only [List.length_append, List.length_replicate]; word
    wp_auto
    rw [ite_eq_left ⟨by decide, by word, by word⟩,
      show slice.slice a GoString (W64 0) (i + W64 1) = a by
        rw [show i + W64 1 = a.len by word]; exact (slice_slice_trivial a).symm]
    wp_auto
    iapply HΦ
    iframe
    rw [Hsplit, split_none cur sep Hsep Hnone, Hic, Nat.add_sub_cancel_left,
      show (sint.Z i).toNat = fields.length by word,
      List.replicate_one, List.set_append_right _ _ (Nat.le_refl _), Nat.sub_self]
    simp
    iexact Ha

end proof

end Perennial
