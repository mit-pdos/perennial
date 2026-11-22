/-
The proof of `slices.Concat`.
-/
module

public import Perennial.Spec.slices.Concat
public import Perennial.Spec.slices.Grow

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

/-- The slices of a `zip` of points-tos have the lengths of their lists. -/
theorem zip_ownSlice_lens {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (sls : List GoSlice) (xss : List (List V)) (dq' : DFrac) :
    ([∗list] p ∈ sls.zip xss, (p.1 ↦*{dq'} p.2 : IProp GF)) ⊢
      ⌜∀ (k : Nat) (sl : GoSlice) (xs : List V), sls[k]? = some sl → xss[k]? = some xs →
        xs.length = sint.nat sl.len ∧ 0 ≤ sint.Z sl.len⌝ := by
  induction sls generalizing xss with
  | nil => iintro -; ipureintro; intro k sl xs h; simp at h
  | cons sl sls ih =>
    cases xss with
    | nil => iintro -; ipureintro; intro k sl xs _ h; simp at h
    | cons xs xss =>
      simp only [List.zip_cons_cons]
      iintro H
      icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ H with ⟨H1, H2⟩
      ihave %h1 := ownSlice_len _ _ _ $$ H1
      ihave %h2 := ih xss $$ H2
      ipureintro
      intro k sl' xs' hs hx
      cases k with
      | zero => simp at hs hx; subst hs hx; exact h1
      | succ k => exact h2 k sl' xs' (by simpa using hs) (by simpa using hx)

theorem sum_take_succ_lengths {V : Type} (xss : List (List V)) (k : Nat) (xs : List V)
    (h : xss[k]? = some xs) :
    ((xss.take (k + 1)).map List.length).sum = ((xss.take k).map List.length).sum + xs.length := by
  rw [List.take_add_one, h]; simp

theorem sum_take_le_lengths {V : Type} (xss : List (List V)) (k : Nat) :
    ((xss.take k).map List.length).sum ≤ (xss.map List.length).sum := by
  induction xss generalizing k with
  | nil => simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k => simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; have := ih k; omega

theorem slices.Concat.wp_proof
    (wp_Grow : slices.Grow.spec (GF := GF) (hG := hG)) :
    slices.Concat.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ ss dq sls xss dq' hlen hsum
  wp_start as ⟨Hss, Hels⟩
  ihave %Hlens := zip_ownSlice_lens sls xss dq' $$ Hels
  ihave %Hss_len := ownSlice_len _ _ _ $$ Hss
  wp_auto
  -- the first loop: the sum of the lengths
  ihave IH : iprop(∃ (j : w64) (sv : GoSlice),
      "i" ∷ i_ptr ↦ j ∗ "s" ∷ s_ptr ↦ sv ∗
      "size" ∷ size_ptr ↦ W64 (((xss.take (sint.nat j)).map List.length).sum) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (sls.length : Int)⌝) $$ [i s size]
  · iexists (W64 0), _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.sum_nil]
    iframe
    ipureintro
    exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩
  wp_for IH
  wp_if_destruct
  · ihave %Hss_len := ownSlice_len _ _ _ $$ Hss
    ihave %Hlens := zip_ownSlice_lens sls xss dq' $$ Hels
    have Hlt : sint.nat j < sls.length := by word
    obtain ⟨sl, Hsl⟩ : ∃ sl, sls[sint.nat j]? = some sl := ⟨_, List.getElem?_eq_getElem Hlt⟩
    obtain ⟨xs, Hxs⟩ : ∃ xs, xss[sint.nat j]? = some xs :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have Hxl := Hlens _ _ _ Hsl Hxs
    simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ss.len from ⟨Hj.1, Hif⟩]
    wp_apply wp_load_slice_index ss (sint.Z j) sls dq sl Hj.1 $$ [Hss] as Hss
    · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hsl
    have Hs1 := sum_take_succ_lengths xss _ xs Hxs
    have Hs2 := sum_take_le_lengths xss (sint.nat j + 1)
    have Hsl1 : sint.Z sl.len = xs.length := by rw [Hxl.1]; have := Hxl.2; word
    have Hsz : W64 (((xss.take (sint.nat j)).map List.length).sum) + sl.len =
        W64 ((((xss.take (sint.nat j)).map List.length).sum + xs.length : Nat) : Int) := by
      word
    have Hpos : ¬ sint.Z (W64 (((xss.take (sint.nat j)).map List.length).sum) + sl.len) < sint.Z (W64 0) := by
      rw [Hsz]; word
    rw [decide_eq_false Hpos]
    wp_auto
    wp_for_post
    iframe
    iexists (j + W64 1), _
    rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, Hs1]
    iframe
    rw [Hsz]
    iframe
    ipureintro
    word
  · ihave %Hss_len := ownSlice_len _ _ _ $$ Hss
    have Hjl : sint.nat j = xss.length := by word
    rw [Hjl, List.take_of_length_le (Nat.le_refl _)]
    wp_apply wp_Grow (V := V) (S := S) slice.nil [] (W64 ((xss.map List.length).sum)) $$ []
      as %g ⟨Hg, Hgcap, %Hgc, %Hgnil⟩
    · isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      ipureintro; word
    have Hg0 : xss.flatten = [] → g = slice.nil := by
      intro h
      apply Hgnil
      have : (xss.map List.length).sum = 0 := by
        rw [← List.length_flatten, h]; rfl
      rw [this]; decide
    ihave IH2 : iprop(∃ (j : w64) (nv sv : GoSlice),
        "i" ∷ i_ptr ↦ j ∗ "s" ∷ s_ptr ↦ sv ∗ "newslice" ∷ newslice_ptr ↦ nv ∗
        "Hnv" ∷ nv ↦* (xss.take (sint.nat j)).flatten ∗ "Hnvcap" ∷ ownSliceCap V nv (DFrac.own 1) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ (sls.length : Int)⌝ ∗
        "%Hnil" ∷ ⌜xss.flatten = [] → nv = slice.nil⌝) $$ [i s newslice Hg Hgcap]
    · iexists (W64 0), _, _
      simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.flatten_nil]
      iframe
      ipureintro
      exact ⟨⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega⟩, Hg0⟩
    wp_for IH2
    wp_if_destruct
    · ihave %Hss_len := ownSlice_len _ _ _ $$ Hss
      ihave %Hlens := zip_ownSlice_lens sls xss dq' $$ Hels
      have Hlt : sint.nat j < sls.length := by word
      obtain ⟨sl, Hsl⟩ : ∃ sl, sls[sint.nat j]? = some sl := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨xs, Hxs⟩ : ∃ xs, xss[sint.nat j]? = some xs :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have Hxl := Hlens _ _ _ Hsl Hxs
      have Hz : (sls.zip xss)[sint.nat j]? = some (sl, xs) := by
        simp [List.getElem?_zip_eq_some, Hsl, Hxs]
      simp only [show 0 ≤ sint.Z j ∧ sint.Z j < sint.Z ss.len from ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index ss (sint.Z j) sls dq sl Hj.1 $$ [Hss] as Hss
      · iframe; ipureintro; rw [show (sint.Z j).toNat = sint.nat j by word]; exact Hsl
      icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF) Hz).1 $$ Hels with ⟨Hel, Hback⟩
      have Hfl : (xss.take (sint.nat j + 1)).flatten = (xss.take (sint.nat j)).flatten ++ xs := by
        rw [List.take_add_one, Hxs]; simp
      have Hset : (sls.zip xss).set (sint.nat j) (sl, xs) = sls.zip xss := by
        have h := (List.getElem?_eq_some_iff.mp Hz)
        obtain ⟨hlt, heq⟩ := h
        rw [← heq]; exact List.set_getElem_self hlt
      by_cases Hemp : xss.flatten = []
      · -- everything is empty: `append` of an empty slice onto `nil` is `nil`
        have Hnv := Hnil Hemp
        subst Hnv
        have Hxs0 : xs = [] := by
          rw [List.flatten_eq_nil_iff] at Hemp
          exact Hemp xs (List.mem_of_getElem? Hxs)
        subst Hxs0
        have Hsl0 : sl.len = W64 0 := by
          have h1 := Hxl.1; have h2 := Hxl.2; simp only [List.length_nil] at h1; word
        wp_bind (App (App (Val #(functions go.append [S])) (Val #slice.nil)) (Val #sl))
        iapply wp_slice_append_fits (V := V) (t := Et) slice.nil sl _ ⟨by decide, by word⟩
          (by rw [Hsl0]; decide)
        wp_apply wp_slice_copy_of_len_zero (V := V) (t := Et) _ sl Hsl0
        isplitl []
        · ipureintro; exact isPanic_intoVal _
        imodintro
        have he : slice.slice slice.nil V (W64 0) (slice.nil.len + sl.len) = slice.nil := by
          simp only [slice.slice, sliceIndexRef, Hsl0, show sint.Z (W64 0) = 0 from rfl,
            go.arrayIndexRef_0]
          rfl
        rw [he]
        ispecialize Hback $$ %(sl, []) Hel
        rw [Hset]
        wp_auto
        wp_for_post
        iframe
        iexists (j + W64 1), _, _
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, Hfl, List.append_nil]
        iframe
        ipureintro
        exact ⟨by word, fun _ => rfl⟩
      · wp_apply wp_slice_append (V := V) (t := Et) _ _ sl xs dq' $$ [Hnv Hnvcap Hel]
          with %nv' ⟨Hnv', Hnvcap', Hel⟩
        · iframe Hnv Hnvcap Hel
        ispecialize Hback $$ %(sl, xs) Hel
        rw [Hset]
        wp_for_post
        iframe
        iexists (j + W64 1), _, _
        rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word, Hfl]
        iframe
        ipureintro
        exact ⟨by word, fun h => absurd h Hemp⟩
    · ihave %Hss_len := ownSlice_len _ _ _ $$ Hss
      have Hjl : sint.nat j = xss.length := by word
      rw [Hjl, List.take_of_length_le (Nat.le_refl _)]
      iapply HΦ
      iframe
      ipureintro; exact Hnil

end proof

end Perennial
