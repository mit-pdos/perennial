/-
The proof of `strings.LastIndex`.
-/
module

public import Perennial.Spec.strings.LastIndex
public import Perennial.Spec.internal.bytealg.LastIndexByteString
public import Perennial.Spec.internal.bytealg.HashStrRev
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-- `lastIndexFrom` on a one-byte `sep`, below the length, is `LastIndexByteString`'s loop. -/
private theorem lastIndexFrom_singleton (s : GoString) (c : w8) :
    ∀ j, j < s.length →
      strings.lastIndexFrom s [c] j = internal.bytealg.lastIdxFrom s c (j + 1)
  | 0, hj => by
    have h : ([c] <+: s) ↔ s[0]? = some c := by
      rw [List.singleton_prefix_iff_head?_eq_some, List.head?_eq_getElem?]
    simp only [strings.lastIndexFrom, internal.bytealg.lastIdxFrom, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hj, Option.getD_some]
    rw [List.getElem?_eq_getElem hj] at h
    by_cases hc : s[0] = c
    · simp [h.2 (by rw [hc]), hc]
    · simp [show ¬ [c] <+: s from fun hp => hc (Option.some.inj (h.1 hp)), hc]
  | j + 1, hj => by
    have h : ([c] <+: s.drop (j + 1)) ↔ s[j + 1]? = some c :=
      internal.bytealg.singleton_prefix_drop s c (j + 1)
    rw [List.getElem?_eq_getElem hj] at h
    rw [strings.lastIndexFrom, internal.bytealg.lastIdxFrom,
      lastIndexFrom_singleton s c j (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    by_cases hc : s[j + 1] = c
    · simp [h.2 (by rw [hc]), hc]
    · simp [show ¬ [c] <+: s.drop (j + 1) from fun hp => hc (Option.some.inj (h.1 hp)), hc]

private theorem lastIndex_singleton (s : GoString) (c : w8) :
    strings.lastIndex s [c] = internal.bytealg.lastIndexByte s c := by
  unfold strings.lastIndex internal.bytealg.lastIndexByte
  rcases s.length.eq_zero_or_pos with h | h
  · rw [h]
    rw [List.length_eq_zero_iff] at h
    subst h
    simp [strings.lastIndexFrom, internal.bytealg.lastIdxFrom]
  · obtain ⟨k, hk⟩ : ∃ k, s.length = k + 1 := ⟨s.length - 1, by omega⟩
    rw [hk, strings.lastIndexFrom, lastIndexFrom_singleton s c k (by omega)]
    have : ¬ [c] <+: s.drop (k + 1) := by
      rw [← hk, List.drop_length]; simp
    simp [this]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strings.Assumptions]

set_option maxHeartbeats 800000 in
theorem strings.LastIndex.wp_proof
    (wp_LastIndexByteString : internal.bytealg.LastIndexByteString.spec (GF := GF) (hG := hG))
    (wp_HashStrRev : internal.bytealg.HashStrRev.spec (GF := GF) (hG := hG)) :
    strings.LastIndex.spec (GF := GF) (hG := hG) := by
  intro s sep
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hn
  wp_if_destruct
  · -- `n == 0`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Hsep : sep = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
    subst Hsep
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    rw [strings.lastIndex_nil]
    iapply HΦ
    itrivial
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  have Hn0 : 0 < sep.length := by
    rcases Nat.eq_zero_or_pos sep.length with h | h
    · exact absurd (by rw [h]; rfl) Hif
    · exact h
  wp_if_destruct
  · -- `n == 1`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have H1 : sep.length = 1 := by revert Hif; word
    obtain ⟨c, Hc⟩ : ∃ c, sep = [c] := by
      match sep, H1 with
      | [c], _ => exact ⟨c, rfl⟩
    subst Hc
    try wp_auto
    wp_apply wp_LastIndexByteString as %-
    rw [lastIndex_singleton]
    iapply HΦ
    itrivial
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
  wp_if_destruct
  · -- `n == len(s)`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Heq : sep.length = s.length := by revert Hif; word
    try wp_auto
    wp_if_destruct
    · subst Hif
      try wp_auto
      rw [strings.lastIndex_eq_of sep sep 0 (by omega) (by simp) (fun k hk _ =>
        internal.bytealg.not_prefix_drop_of_long sep sep k Hn0 (by omega))]
      iapply HΦ
      itrivial
    · try wp_auto
      rw [strings.lastIndex_eq_neg s sep (fun k _ hk => by
        rcases Nat.eq_zero_or_pos k with h | h
        · subst h
          exact Hif (List.IsPrefix.eq_of_length (by simpa using hk) Heq)
        · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega) hk)]
      iapply HΦ
      itrivial
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · -- `n > len(s)`
    simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
    have Hgt : s.length < sep.length := by revert Hif; word
    try wp_auto
    rw [strings.lastIndex_eq_neg s sep (fun k _ =>
      internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega))]
    iapply HΦ
    itrivial
  simp only [eq_comm (a := true), decide_eq_true_eq] at Hif
  have Hlt : sep.length < s.length := by revert Hif; word
  try wp_auto
  wp_apply wp_HashStrRev
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  try wp_auto
  rw [show W64 (s.length : Int) - W64 (sep.length : Int) =
    W64 ((s.length - sep.length : Nat) : Int) by word]
  -- the first loop: the hash of the reverse of `s[last:]`
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 ((j : Int) - 1) ∗
      "h" ∷ h_ptr ↦ internal.bytealg.hashStrRev (s.drop j) ∗
      "%Hj" ∷ ⌜s.length - sep.length ≤ j ∧ j ≤ s.length⌝ : IProp GF) $$ [i h]
  · iexists s.length
    isplitl [i]
    · rw [show W64 ((s.length : Int) - 1) = W64 (s.length : Int) - W64 1 by word]
      iexact i
    isplitl [h]
    · rw [show internal.bytealg.hashStrRev (List.drop s.length s) = zero_val w32 by
        simp [internal.bytealg.hashStrRev, internal.bytealg.hashStr]; rfl]
      iexact h
    ipureintro; omega
  wp_for HI
  wp_if_destruct
  · rcases j with _ | k
    · exfalso; revert Hif; word
    have Hk : sint.nat (W64 (((k + 1 : Nat) : Int) - 1)) = k := by word
    have Hk0 : 0 ≤ sint.Z (W64 (((k + 1 : Nat) : Int) - 1)) := by word
    have Hks : k < s.length := by omega
    obtain ⟨b, Hb⟩ : ∃ b, s[k]? = some b := ⟨_, List.getElem?_eq_getElem Hks⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_for_post
    iframe
    iexists k
    isplitl [i]
    · rw [show W64 ((k : Int) - 1) = W64 (((k + 1 : Nat) : Int) - 1) - W64 1 by word]
      iexact i
    isplitl [h]
    · rw [show s.drop k = b :: s.drop (k + 1) by
          rw [List.drop_eq_getElem_cons Hks]; simp [List.getElem?_eq_getElem Hks] at Hb; rw [Hb],
        internal.bytealg.hashStrRev_cons]
      iexact h
    ipureintro
    have : s.length - sep.length ≤ k := by revert Hif; word
    omega
  have Hjl : j = s.length - sep.length := by have := Hj; revert Hif; word
  subst Hjl
  have Hwin : (s.drop (s.length - sep.length)).take sep.length = s.drop (s.length - sep.length) :=
    List.take_of_length_le (by simp; omega)
  try wp_auto
  wp_join (Q := fun v => iprop(⌜v = #(decide (sep <+: s.drop (s.length - sep.length)))⌝ ∗
      s_ptr ↦ s ∗ last_ptr ↦ W64 ((s.length - sep.length : Nat) : Int) ∗ substr_ptr ↦ sep))
      at (if: #(decide _) then _ else #false) with [s last substr]
  · wp_if_destruct
    · wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      rw [ite_eq_left (by word)]
      rw [show sint.nat (W64 (s.length : Int)) - sint.nat (W64 ((s.length - sep.length : Nat) : Int))
          = sep.length by word,
        show sint.nat (W64 ((s.length - sep.length : Nat) : Int)) = s.length - sep.length by word,
        Hwin]
      try wp_auto
      iframe
      ipureintro
      rw [decide_eq_decide.2 (show s.drop (s.length - sep.length) = sep ↔
        sep <+: s.drop (s.length - sep.length) by
          rw [List.prefix_iff_eq_take, Hwin]; exact eq_comm)]
    · iframe
      ipureintro
      rw [decide_eq_false (fun h => Hif (by
        have e : s.drop (s.length - sep.length) = sep := by
          rw [← Hwin]; exact (List.prefix_iff_eq_take.1 h).symm
        rw [e]))]
  iintro ⟨%Hv, s, last, substr⟩
  subst Hv
  try wp_auto
  wp_if_destruct
  · -- found at `last`
    try wp_auto
    rw [strings.lastIndex_eq_of s sep (s.length - sep.length) (by omega) Hif (fun k hk _ =>
      internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega))]
    iapply HΦ
    itrivial
  -- the second loop
  try wp_auto
  ihave HJ : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 ((j : Int) - 1) ∗
      "h" ∷ h_ptr ↦ internal.bytealg.hashStrRev ((s.drop j).take sep.length) ∗
      "%Hj" ∷ ⌜j ≤ s.length - sep.length ∧
        ∀ k, j ≤ k → k ≤ s.length → ¬ sep <+: s.drop k⌝ : IProp GF) $$ [i h]
  · iexists s.length - sep.length
    isplitl [i]
    · rw [show W64 (((s.length - sep.length : Nat) : Int) - 1) =
        W64 ((s.length - sep.length : Nat) : Int) - W64 1 by word]
      iexact i
    isplitl [h]
    · rw [Hwin]; iexact h
    ipureintro
    refine ⟨Nat.le_refl _, fun k hk _ => ?_⟩
    rcases Nat.lt_or_ge (s.length - sep.length) k with h | h
    · exact internal.bytealg.not_prefix_drop_of_long s sep k Hn0 (by omega)
    · rw [show k = s.length - sep.length by omega]; exact Hif
  wp_for HJ
  wp_if_destruct
  · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    rcases j with _ | k
    · exfalso; revert Hif; word
    have Hk : sint.nat (W64 (((k + 1 : Nat) : Int) - 1)) = k := by word
    have Hk0 : 0 ≤ sint.Z (W64 (((k + 1 : Nat) : Int) - 1)) := by word
    rw [show W64 (((k + 1 : Nat) : Int) - 1) = W64 (k : Int) by word] at Hk Hk0 ⊢
    have Hkn : k + sep.length < s.length := by omega
    obtain ⟨x, Hx⟩ : ∃ x, s[k]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨y, Hy⟩ : ∃ y, s[k + sep.length]? = some y := ⟨_, List.getElem?_eq_getElem Hkn⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hx]
    try wp_auto
    simp only [show sint.nat (W64 (k : Int) + W64 (sep.length : Int)) = k + sep.length by word,
      show 0 ≤ sint.Z (W64 (k : Int) + W64 (sep.length : Int)) by word, ↓reduceIte, Hy]
    try wp_auto
    rw [internal.bytealg.hashStrRev_window_roll s sep.length k x y Hn0 Hx Hy]
    wp_join (Q := fun v => iprop(⌜v = #(decide (sep <+: s.drop k))⌝ ∗
        s_ptr ↦ s ∗ i_ptr ↦ W64 (k : Int) ∗ n_ptr ↦ W64 (sep.length : Int) ∗ substr_ptr ↦ sep))
        at (if: #(decide _) then _ else #false) with [s i n substr]
    · wp_if_destruct
      · try wp_auto
        rw [ite_eq_left (by word)]
        rw [show sint.nat (W64 (k : Int) + W64 (sep.length : Int)) - sint.nat (W64 (k : Int)) =
            sep.length by word, show sint.nat (W64 (k : Int)) = k by word]
        try wp_auto
        iframe
        ipureintro
        rw [decide_eq_decide.2 (show List.take sep.length (List.drop k s) = sep ↔
          sep <+: List.drop k s by rw [List.prefix_iff_eq_take]; exact eq_comm)]
      · iframe
        ipureintro
        rw [decide_eq_false (fun h => Hif (by
          have e : (s.drop k).take sep.length = sep := (List.prefix_iff_eq_take.1 h).symm
          rw [e]))]
    iintro ⟨%Hv, s, i, n, substr⟩
    subst Hv
    try wp_auto
    wp_if_destruct
    · -- found at `i`
      try wp_auto
      wp_for_post
      rw [strings.lastIndex_eq_of s sep k (by omega) Hif (fun k' hk' hk's =>
        Hj.2 k' (by omega) hk's)]
      iapply HΦ
      itrivial
    · try wp_auto
      wp_for_post
      iframe
      iexists k
      isplitl [i]
      · rw [show W64 ((k : Int) - 1) = W64 (k : Int) - W64 1 by word]
        iexact i
      iframe
      ipureintro
      refine ⟨by omega, fun k' hk' hk's => ?_⟩
      rcases Nat.lt_or_ge k k' with h | h
      · exact Hj.2 k' (by omega) hk's
      · rw [show k' = k by omega]; exact Hif
  · -- `i < 0`: no occurrence
    try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hj0 : j = 0 := by have := Hj.1; revert Hif; word
    subst Hj0
    try wp_auto
    rw [strings.lastIndex_eq_neg s sep (fun k hk => Hj.2 k (Nat.zero_le _) hk)]
    iapply HΦ
    itrivial

end proof

end Perennial
