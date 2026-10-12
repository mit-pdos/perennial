/-
The proof of `internal.stringslite.Index'`.
-/
module

public import Perennial.Spec.internal.stringslite.Index
public import Perennial.Spec.internal.stringslite.IndexByte
public import Perennial.Spec.internal.bytealg.IndexString
public import Perennial.Spec.internal.bytealg.Cutover
public import Perennial.Spec.internal.bytealg.IndexRabinKarp
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.stringslite.Assumptions]

set_option maxHeartbeats 8000000 in
theorem internal.stringslite.Index'.wp_proof
    (wp_IndexByte : internal.stringslite.IndexByte.spec (GF := GF) (hG := hG))
    (wp_IndexString : internal.bytealg.IndexString.spec (GF := GF) (hG := hG))
    (wp_Cutover : internal.bytealg.Cutover.spec (GF := GF) (hG := hG))
    (wp_IndexRabinKarp : internal.bytealg.IndexRabinKarp.spec (GF := GF) (hG := hG)) :
    internal.stringslite.Index'.spec (GF := GF) (hG := hG) := fun s sub => by
  wp_start as #Hinit
  ihave #Hb : isPkgInit (PROP := IProp GF) pkg_id.internal.bytealg $$ []
  · iPkgInit
  ihave Hm := internal.bytealg.isInit_access $$ Hb
  icases Hm with ⟨%m, #HM, %Hm⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hsub
  have Hn : sint.Z (W64 sub.length) = sub.length := by word
  -- case `n == 0`
  wp_if_destruct
  · have H := of_decide_eq_true Hif.symm
    have : sub = [] := List.eq_nil_of_length_eq_zero (by word)
    subst this
    rw [internal.bytealg.indexResult_nil]
    iapply HΦ; itrivial
  have Hn0 : sub.length ≠ 0 := fun h => Hif (by simp [h])
  -- case `n == 1`
  wp_if_destruct
  · have H := of_decide_eq_true Hif.symm
    have H1 : sub.length = 1 := by word
    obtain ⟨c, rfl⟩ : ∃ c, sub = [c] := List.length_eq_one_iff.1 H1
    simp only [List.getElem?_cons_zero]
    wp_auto
    wp_apply wp_IndexByte
    iapply HΦ; itrivial
  have Hn1 : sub.length ≠ 1 := fun h => Hif (by simp [h])
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  -- case `n == len(s)`
  wp_if_destruct
  · have H := of_decide_eq_true Hif.symm
    have hlen : sub.length = s.length := by word
    rw [internal.bytealg.indexResult_of_length_ge s sub (by omega)]
    wp_if_destruct
    · rw [ite_eq_left Hif]; iapply HΦ; itrivial
    · rw [ite_eq_right Hif]; iapply HΦ; itrivial
  have Hns : sub.length ≠ s.length := fun h => Hif (by simp [h])
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  -- case `n > len(s)`
  wp_if_destruct
  · have H := of_decide_eq_true Hif.symm
    rw [internal.bytealg.indexResult_of_length_ge s sub (by word),
      ite_eq_right (fun h => Hns (by rw [h]))]
    iapply HΦ; itrivial
  have Hlt : sub.length < s.length := by
    have : ¬ sint.Z (W64 s.length) < sint.Z (W64 sub.length) :=
      fun h => Hif (by rw [decide_eq_true h])
    word
  have Hn2 : 2 ≤ sub.length := by omega
  obtain ⟨c0, c1, rest, rfl⟩ : ∃ c0 c1 rest, sub = c0 :: c1 :: rest := by
    match sub, Hn2 with
    | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
  -- case `n <= bytealg.MaxLen`
  wp_if_destruct
  · have HnM : (c0 :: c1 :: rest).length ≤ sint.Z m := by
      have := of_decide_eq_true Hif.symm; word
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    wp_if_destruct
    · -- `len(s) <= bytealg.MaxBruteForce`
      wp_apply wp_IndexString s _ m ⟨Hn2, HnM⟩ $$ [HM]
      · iexact HM
      iapply HΦ; itrivial
    -- the scan for `c0`, then `c1` and the rest
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
    have HT : sint.Z (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1) =
        s.length - (c0 :: c1 :: rest).length + 1 := by word
    ihave IH : iprop(∃ (i fails : w64),
        "i" ∷ i_ptr ↦ i ∗
        "fails" ∷ fails_ptr ↦ fails ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ s.length - (c0 :: c1 :: rest).length + 1 ∧
          ∀ j, j < sint.nat i → ¬ (c0 :: c1 :: rest) <+: s.drop j⌝) $$ [i fails]
    · iexists _, _
      iframe
      ipureintro
      exact ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
    wp_for IH
    wp_if_destruct
    · rw [HT] at Hif
      have HiT := Hif
      have hI : sint.nat i < s.length := by simp at Hn2; word
      obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hI⟩
      simp only [Hi.1, ↓reduceIte, hb]
      wp_auto
      -- skip to the next `c0`
      wp_join (Q := fun v => iprop(
          (⌜v = returnVal #(W64 (-1)) ∧
              internal.bytealg.indexResult s (c0 :: c1 :: rest) = W64 (-1)⌝ ∨
            ∃ i' : w64, ⌜v = executeVal⌝ ∗ i_ptr ↦ i' ∗
              ⌜sint.Z i ≤ sint.Z i' ∧ sint.Z i' < s.length - (c0 :: c1 :: rest).length + 1 ∧
                s[sint.nat i']? = some c0 ∧
                ∀ j, j < sint.nat i' → ¬ (c0 :: c1 :: rest) <+: s.drop j⌝) ∗
          s_ptr ↦ s ∗ c0_ptr ↦ c0 ∗
          t_ptr ↦ (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1)))
        with [i s c0 t]
      · -- `s[i] == c0`
        iframe
        iright
        iexists i
        iframe
        ipureintro
        exact ⟨Int.le_refl _, HiT, by rw [hb, Hif], Hi.2.2⟩
      · -- `s[i] != c0`: `IndexByte(s[i+1:t], c0)`
        rw [ite_eq_left ⟨by word, by rw [HT]; word, by rw [HT]; word⟩,
          show sint.nat (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1) =
            s.length - (c0 :: c1 :: rest).length + 1 by word,
          show sint.nat (i + W64 1) = sint.nat i + 1 by word]
        wp_auto
        wp_apply wp_IndexByte
        -- no occurrence at `i`: `s[i] != c0`
        have Hno_i : ¬ (c0 :: c1 :: rest) <+: s.drop (sint.nat i) := fun h =>
          Hif (by have := internal.bytealg.occ_head _ _ _ _ h; rw [hb] at this; cases this; rfl)
        rcases internal.bytealg.indexResult_cases
            ((s.drop (sint.nat i + 1)).take
              (s.length - (c0 :: c1 :: rest).length + 1 - (sint.nat i + 1))) [c0]
          with ⟨k, hk, hres, hkle⟩ | ⟨hk, hres⟩
        · -- the next `c0` is at `i + 1 + k`
          obtain ⟨-, hocc, hmin⟩ := (internal.bytealg.firstOcc_eq_some_iff _ _ _).1 hk
          rw [occ_slice_singleton s c0 _ _ _] at hocc
          simp only [List.length_take, List.length_drop] at hkle
          rw [hres, decide_eq_false (show ¬ sint.Z (W64 k) < sint.Z (W64 0) by word)]
          wp_auto
          iframe
          iright
          iexists _
          iframe
          ipureintro
          have Hi' : sint.nat (i + (W64 k + W64 1)) = sint.nat i + 1 + k := by word
          refine ⟨rfl, by word, by word, by rw [Hi']; exact hocc.2, fun j hj => ?_⟩
          rw [Hi'] at hj
          rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
          · exact Hi.2.2 j hj'
          rcases Nat.eq_or_lt_of_le hj' with rfl | hj'
          · exact Hno_i
          · intro h
            have := internal.bytealg.occ_head _ _ _ _ h
            apply hmin (j - (sint.nat i + 1)) (by omega)
            rw [occ_slice_singleton s c0 _ _ _,
              show sint.nat i + 1 + (j - (sint.nat i + 1)) = j by omega]
            exact ⟨by omega, this⟩
        · -- no `c0` in `s[i+1:t]`: `substr` occurs nowhere
          rw [hres]
          wp_auto
          iframe
          ileft
          ipureintro
          refine ⟨rfl, internal.bytealg.indexResult_of_none _ _ fun j hj h => ?_⟩
          rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
          · exact Hi.2.2 j hj' h
          rcases Nat.eq_or_lt_of_le hj' with rfl | hj'
          · exact Hno_i h
          rcases Nat.lt_or_ge j (s.length - (c0 :: c1 :: rest).length + 1) with hjT | hjT
          · have := internal.bytealg.occ_head _ _ _ _ h
            apply (internal.bytealg.firstOcc_eq_none_iff _ _).1 hk (j - (sint.nat i + 1))
              (by simp only [List.length_take, List.length_drop]
                  simp only [List.length_cons] at *; omega)
            rw [occ_slice_singleton s c0 _ _ _,
              show sint.nat i + 1 + (j - (sint.nat i + 1)) = j by omega]
            exact ⟨by omega, this⟩
          · exact internal.bytealg.not_occ_of_short _ _ (by simp) j (by simp at hjT ⊢; omega) h
      iintro ⟨Hv, s, c0, t⟩
      icases Hv with (%Hv | ⟨%i', %Hv, i, %Hi'⟩)
      · -- `IndexByte` found no `c0`: return `-1`
        obtain ⟨rfl, Hres⟩ := Hv
        wp_auto
        wp_for_post
        rw [Hres]
        iapply HΦ; itrivial
      subst Hv
      wp_auto
      obtain ⟨Hii', Hi'T, Hc0, Hno⟩ := Hi'
      have hI' : sint.nat i' + 1 < s.length := by simp only [List.length_cons] at *; word
      obtain ⟨b1, hb1⟩ : ∃ b, s[sint.nat i' + 1]? = some b :=
        ⟨_, List.getElem?_eq_getElem hI'⟩
      simp only [show 0 ≤ sint.Z (i' + W64 1) by word, ↓reduceIte,
        show sint.nat (i' + W64 1) = sint.nat i' + 1 by word, hb1]
      wp_auto
      -- an occurrence at `i'`?
      wp_join (Q := fun v => iprop(
          (⌜v = returnVal #i' ∧ internal.bytealg.indexResult s (c0 :: c1 :: rest) = i'⌝ ∨
            ⌜v = executeVal ∧ ¬ (c0 :: c1 :: rest) <+: s.drop (sint.nat i')⌝) ∗
          s_ptr ↦ s ∗ i_ptr ↦ i' ∗ c1_ptr ↦ c1 ∗ n_ptr ↦ W64 (c0 :: c1 :: rest).length ∗
          substr_ptr ↦ (c0 :: c1 :: rest)))
        with [s i c1 n substr]
      · -- `s[i'+1] == c1`: compare `s[i':i'+n]`
        rw [ite_eq_left ⟨by word, by word, by simp only [List.length_cons] at *; word⟩,
          show sint.nat (i' + W64 (c0 :: c1 :: rest).length) - sint.nat i' =
            (c0 :: c1 :: rest).length by word]
        wp_auto
        wp_if_destruct
        · iframe
          ileft
          ipureintro
          exact ⟨by simp, internal.bytealg.indexResult_of_occ _ _ _ (by word) (by word)
            ((internal.bytealg.slice_eq_iff_occ _ _ _).1 Hif) Hno⟩
        · iframe
          iright
          ipureintro
          exact ⟨by simp, fun h => Hif ((internal.bytealg.slice_eq_iff_occ _ _ _).2 h)⟩
      · -- `s[i'+1] != c1`
        iframe
        iright
        ipureintro
        refine ⟨by simp, fun h => Hif ?_⟩
        have := internal.bytealg.occ_second _ _ _ _ _ h
        rw [hb1] at this
        cases this; rfl
      iintro ⟨Hv, s, i, c1, n, substr⟩
      icases Hv with (%Hv | %Hv)
      · -- an occurrence at `i'`, the first
        obtain ⟨rfl, Hres⟩ := Hv
        wp_auto
        wp_for_post
        rw [Hres]
        iapply HΦ; itrivial
      obtain ⟨rfl, Hno_i'⟩ := Hv
      wp_auto
      have Hno' : ∀ j, j < sint.nat i' + 1 → ¬ (c0 :: c1 :: rest) <+: s.drop j := by
        intro j hj
        rcases Nat.lt_or_ge j (sint.nat i') with hj' | hj'
        · exact Hno j hj'
        · obtain rfl : j = sint.nat i' := by omega
          exact Hno_i'
      wp_apply wp_Cutover as %r _
      wp_if_destruct
      · -- too many false positives: `IndexString(s[i'+1:], substr)`
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        rw [ite_eq_left ⟨by word, by word, by word⟩,
          show sint.nat (i' + W64 1) = sint.nat i' + 1 by word,
          List.take_of_length_le (by simp; word)]
        wp_auto
        wp_apply wp_IndexString _ _ m ⟨Hn2, HnM⟩ $$ [HM]
        · iexact HM
        have Hdrop := internal.bytealg.firstOcc_drop s (c0 :: c1 :: rest) (sint.nat i' + 1)
          (by omega) Hno'
        rcases internal.bytealg.indexResult_cases (s.drop (sint.nat i' + 1)) (c0 :: c1 :: rest)
          with ⟨k, hk, hres, hkle⟩ | ⟨hk, hres⟩
        · rw [hres, decide_eq_true (show sint.Z (W64 0) ≤ sint.Z (W64 k) by
            simp at hkle; word)]
          wp_auto
          wp_for_post
          rw [show internal.bytealg.indexResult s (c0 :: c1 :: rest) = W64 k + (i' + W64 1) by
            unfold internal.bytealg.indexResult; rw [Hdrop, hk]; simp at hkle ⊢; word]
          iapply HΦ; itrivial
        · rw [hres]
          wp_auto
          wp_for_post
          rw [show internal.bytealg.indexResult s (c0 :: c1 :: rest) = W64 (-1) by
            unfold internal.bytealg.indexResult; rw [Hdrop, hk]; rfl]
          iapply HΦ; itrivial
      · -- on to `i' + 1`
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun j hj => Hno' j (by
          rw [show sint.nat (i' + W64 1) = sint.nat i' + 1 by word] at hj; exact hj)⟩
    · -- `i >= t`: no occurrence
      rw [HT] at Hif
      rw [internal.bytealg.indexResult_of_none _ _ fun j hj h => ?_]
      · iapply HΦ; itrivial
      rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
      · exact Hi.2.2 j hj' h
      · exact internal.bytealg.not_occ_of_short _ _ (by simp) j
          (by simp only [List.length_cons] at *; word) h
  -- case `n > bytealg.MaxLen`: the same scan, then Rabin-Karp
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  have HT : sint.Z (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1) =
      s.length - (c0 :: c1 :: rest).length + 1 := by word
  ihave IH : iprop(∃ (i fails : w64),
      "i" ∷ i_ptr ↦ i ∗
      "fails" ∷ fails_ptr ↦ fails ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ s.length - (c0 :: c1 :: rest).length + 1 ∧
        ∀ j, j < sint.nat i → ¬ (c0 :: c1 :: rest) <+: s.drop j⌝) $$ [i fails]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by decide, by word, fun j hj => by simp at hj; omega⟩
  wp_for IH
  wp_if_destruct
  · rw [HT] at Hif
    have HiT := Hif
    have hI : sint.nat i < s.length := by simp at Hn2; word
    obtain ⟨b, hb⟩ : ∃ b, s[sint.nat i]? = some b := ⟨_, List.getElem?_eq_getElem hI⟩
    simp only [Hi.1, ↓reduceIte, hb]
    wp_auto
    -- skip to the next `c0`
    wp_join (Q := fun v => iprop(
        (⌜v = returnVal #(W64 (-1)) ∧
            internal.bytealg.indexResult s (c0 :: c1 :: rest) = W64 (-1)⌝ ∨
          ∃ i' : w64, ⌜v = executeVal⌝ ∗ i_ptr ↦ i' ∗
            ⌜sint.Z i ≤ sint.Z i' ∧ sint.Z i' < s.length - (c0 :: c1 :: rest).length + 1 ∧
              s[sint.nat i']? = some c0 ∧
              ∀ j, j < sint.nat i' → ¬ (c0 :: c1 :: rest) <+: s.drop j⌝) ∗
        s_ptr ↦ s ∗ c0_ptr ↦ c0 ∗
        t_ptr ↦ (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1)))
      with [i s c0 t]
    · -- `s[i] == c0`
      iframe
      iright
      iexists i
      iframe
      ipureintro
      exact ⟨Int.le_refl _, HiT, by rw [hb, Hif], Hi.2.2⟩
    · -- `s[i] != c0`: `IndexByte(s[i+1:t], c0)`
      rw [ite_eq_left ⟨by word, by rw [HT]; word, by rw [HT]; word⟩,
        show sint.nat (W64 s.length - W64 (c0 :: c1 :: rest).length + W64 1) =
          s.length - (c0 :: c1 :: rest).length + 1 by word,
        show sint.nat (i + W64 1) = sint.nat i + 1 by word]
      wp_auto
      wp_apply wp_IndexByte
      -- no occurrence at `i`: `s[i] != c0`
      have Hno_i : ¬ (c0 :: c1 :: rest) <+: s.drop (sint.nat i) := fun h =>
        Hif (by have := internal.bytealg.occ_head _ _ _ _ h; rw [hb] at this; cases this; rfl)
      rcases internal.bytealg.indexResult_cases
          ((s.drop (sint.nat i + 1)).take
            (s.length - (c0 :: c1 :: rest).length + 1 - (sint.nat i + 1))) [c0]
        with ⟨k, hk, hres, hkle⟩ | ⟨hk, hres⟩
      · -- the next `c0` is at `i + 1 + k`
        obtain ⟨-, hocc, hmin⟩ := (internal.bytealg.firstOcc_eq_some_iff _ _ _).1 hk
        rw [occ_slice_singleton s c0 _ _ _] at hocc
        simp only [List.length_take, List.length_drop] at hkle
        rw [hres, decide_eq_false (show ¬ sint.Z (W64 k) < sint.Z (W64 0) by word)]
        wp_auto
        iframe
        iright
        iexists _
        iframe
        ipureintro
        have Hi' : sint.nat (i + (W64 k + W64 1)) = sint.nat i + 1 + k := by word
        refine ⟨rfl, by word, by word, by rw [Hi']; exact hocc.2, fun j hj => ?_⟩
        rw [Hi'] at hj
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact Hi.2.2 j hj'
        rcases Nat.eq_or_lt_of_le hj' with rfl | hj'
        · exact Hno_i
        · intro h
          have := internal.bytealg.occ_head _ _ _ _ h
          apply hmin (j - (sint.nat i + 1)) (by omega)
          rw [occ_slice_singleton s c0 _ _ _,
            show sint.nat i + 1 + (j - (sint.nat i + 1)) = j by omega]
          exact ⟨by omega, this⟩
      · -- no `c0` in `s[i+1:t]`: `substr` occurs nowhere
        rw [hres]
        wp_auto
        iframe
        ileft
        ipureintro
        refine ⟨rfl, internal.bytealg.indexResult_of_none _ _ fun j hj h => ?_⟩
        rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
        · exact Hi.2.2 j hj' h
        rcases Nat.eq_or_lt_of_le hj' with rfl | hj'
        · exact Hno_i h
        rcases Nat.lt_or_ge j (s.length - (c0 :: c1 :: rest).length + 1) with hjT | hjT
        · have := internal.bytealg.occ_head _ _ _ _ h
          apply (internal.bytealg.firstOcc_eq_none_iff _ _).1 hk (j - (sint.nat i + 1))
            (by simp only [List.length_take, List.length_drop]
                simp only [List.length_cons] at *; omega)
          rw [occ_slice_singleton s c0 _ _ _,
            show sint.nat i + 1 + (j - (sint.nat i + 1)) = j by omega]
          exact ⟨by omega, this⟩
        · exact internal.bytealg.not_occ_of_short _ _ (by simp) j (by simp at hjT ⊢; omega) h
    iintro ⟨Hv, s, c0, t⟩
    icases Hv with (%Hv | ⟨%i', %Hv, i, %Hi'⟩)
    · -- `IndexByte` found no `c0`: return `-1`
      obtain ⟨rfl, Hres⟩ := Hv
      wp_auto
      wp_for_post
      rw [Hres]
      iapply HΦ; itrivial
    subst Hv
    wp_auto
    obtain ⟨Hii', Hi'T, Hc0, Hno⟩ := Hi'
    have hI' : sint.nat i' + 1 < s.length := by simp only [List.length_cons] at *; word
    obtain ⟨b1, hb1⟩ : ∃ b, s[sint.nat i' + 1]? = some b :=
      ⟨_, List.getElem?_eq_getElem hI'⟩
    simp only [show 0 ≤ sint.Z (i' + W64 1) by word, ↓reduceIte,
      show sint.nat (i' + W64 1) = sint.nat i' + 1 by word, hb1]
    wp_auto
    -- an occurrence at `i'`?
    wp_join (Q := fun v => iprop(
        (⌜v = returnVal #i' ∧ internal.bytealg.indexResult s (c0 :: c1 :: rest) = i'⌝ ∨
          ⌜v = executeVal ∧ ¬ (c0 :: c1 :: rest) <+: s.drop (sint.nat i')⌝) ∗
        s_ptr ↦ s ∗ i_ptr ↦ i' ∗ c1_ptr ↦ c1 ∗ n_ptr ↦ W64 (c0 :: c1 :: rest).length ∗
        substr_ptr ↦ (c0 :: c1 :: rest)))
      with [s i c1 n substr]
    · -- `s[i'+1] == c1`: compare `s[i':i'+n]`
      rw [ite_eq_left ⟨by word, by word, by simp only [List.length_cons] at *; word⟩,
        show sint.nat (i' + W64 (c0 :: c1 :: rest).length) - sint.nat i' =
          (c0 :: c1 :: rest).length by word]
      wp_auto
      wp_if_destruct
      · iframe
        ileft
        ipureintro
        exact ⟨by simp, internal.bytealg.indexResult_of_occ _ _ _ (by word) (by word)
          ((internal.bytealg.slice_eq_iff_occ _ _ _).1 Hif) Hno⟩
      · iframe
        iright
        ipureintro
        exact ⟨by simp, fun h => Hif ((internal.bytealg.slice_eq_iff_occ _ _ _).2 h)⟩
    · -- `s[i'+1] != c1`
      iframe
      iright
      ipureintro
      refine ⟨by simp, fun h => Hif ?_⟩
      have := internal.bytealg.occ_second _ _ _ _ _ h
      rw [hb1] at this
      cases this; rfl
    iintro ⟨Hv, s, i, c1, n, substr⟩
    icases Hv with (%Hv | %Hv)
    · -- an occurrence at `i'`, the first
      obtain ⟨rfl, Hres⟩ := Hv
      wp_auto
      wp_for_post
      rw [Hres]
      iapply HΦ; itrivial
    obtain ⟨rfl, Hno_i'⟩ := Hv
    wp_auto
    have Hno' : ∀ j, j < sint.nat i' + 1 → ¬ (c0 :: c1 :: rest) <+: s.drop j := by
      intro j hj
      rcases Nat.lt_or_ge j (sint.nat i') with hj' | hj'
      · exact Hno j hj'
      · obtain rfl : j = sint.nat i' := by omega
        exact Hno_i'
    -- `fails >= 4+i>>4 && i < t`: too many false positives, Rabin-Karp on `s[i'+1:]`
    wp_if_destruct
    · wp_if_destruct
      · have HiT' : sint.nat i' + 1 < s.length - (c0 :: c1 :: rest).length + 1 := by
          rw [HT] at Hif; word
        wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
        rw [ite_eq_left ⟨by word, by word, by word⟩,
          show sint.nat (i' + W64 1) = sint.nat i' + 1 by word,
          List.take_of_length_le (by simp; word)]
        wp_auto
        wp_apply wp_IndexRabinKarp _ _ (by simp only [List.length_drop]; omega)
        have Hdrop := internal.bytealg.firstOcc_drop s (c0 :: c1 :: rest) (sint.nat i' + 1)
          (by omega) Hno'
        rcases internal.bytealg.indexResult_cases (s.drop (sint.nat i' + 1)) (c0 :: c1 :: rest)
          with ⟨k, hk, hres, hkle⟩ | ⟨hk, hres⟩
        · rw [hres, decide_eq_false (show ¬ sint.Z (W64 k) < sint.Z (W64 0) by
            simp at hkle; word)]
          wp_auto
          wp_for_post
          rw [show internal.bytealg.indexResult s (c0 :: c1 :: rest) = (i' + W64 1) + W64 k by
            unfold internal.bytealg.indexResult; rw [Hdrop, hk]; simp at hkle ⊢; word]
          iapply HΦ; itrivial
        · rw [hres]
          wp_auto
          wp_for_post
          rw [show internal.bytealg.indexResult s (c0 :: c1 :: rest) = W64 (-1) by
            unfold internal.bytealg.indexResult; rw [Hdrop, hk]; rfl]
          iapply HΦ; itrivial
      · -- on to `i' + 1`
        wp_for_post
        iframe
        iexists _, _
        iframe
        ipureintro
        refine ⟨by word, by word, fun j hj => Hno' j (by
          rw [show sint.nat (i' + W64 1) = sint.nat i' + 1 by word] at hj; exact hj)⟩
    · -- on to `i' + 1`
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨by word, by word, fun j hj => Hno' j (by
        rw [show sint.nat (i' + W64 1) = sint.nat i' + 1 by word] at hj; exact hj)⟩
  · -- `i >= t`: no occurrence
    rw [HT] at Hif
    rw [internal.bytealg.indexResult_of_none _ _ fun j hj h => ?_]
    · iapply HΦ; itrivial
    rcases Nat.lt_or_ge j (sint.nat i) with hj' | hj'
    · exact Hi.2.2 j hj' h
    · exact internal.bytealg.not_occ_of_short _ _ (by simp) j
        (by simp only [List.length_cons] at *; word) h

end proof

end Perennial
