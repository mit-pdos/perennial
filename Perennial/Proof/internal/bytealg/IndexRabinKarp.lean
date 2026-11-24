/-
The proof of `internal.bytealg.IndexRabinKarp` (at `string`).
-/
module

public import Perennial.Spec.internal.bytealg.IndexRabinKarp
public import Perennial.Spec.internal.bytealg.HashStr
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : internal.bytealg.Assumptions]

theorem internal.bytealg.IndexRabinKarp.wp_proof
    (wp_HashStr : internal.bytealg.HashStr.spec (GF := GF) (hG := hG)) :
    internal.bytealg.IndexRabinKarp.spec (GF := GF) (hG := hG) := by
  intro s sep
  wp_start as %Hle
  wp_auto
  wp_apply wp_HashStr
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsepl
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "h" ∷ h_ptr ↦ internal.bytealg.hashStr (s.take j) ∗
      "%Hj" ∷ ⌜j ≤ sep.length⌝ : IProp GF) $$ [i h]
  · iexists 0
    iframe i
    isplitl
    · rw [show internal.bytealg.hashStr (List.take 0 s) = zero_val w32 by
        simp [internal.bytealg.hashStr]; rfl]
      iexact h
    ipureintro; exact Nat.zero_le _
  wp_for HI
  wp_if_destruct
  · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j < sep.length := by have := Hj; revert Hif; word
    have Hk : sint.nat (W64 (j : Int)) = j := by word
    have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    have Hjs : j < s.length := by omega
    obtain ⟨b, Hb⟩ : ∃ b, s[j]? = some b := ⟨_, List.getElem?_eq_getElem Hjs⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_for_post
    iframe
    iexists j + 1
    isplitl [i]
    · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
      iexact i
    isplitl [h]
    · rw [List.take_add_one, Hb, Option.toList_some, internal.bytealg.hashStr_append_singleton]
      iexact h
    ipureintro; omega
  · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j = sep.length := by have := Hj; revert Hif; word
    try simp only [Hif, decide_false, intoVal_eq_iff, decide_true, ↓reduceIte]
    subst Hjl
    try wp_auto
    wp_join (Q := fun v => iprop(⌜v = #(decide (List.take sep.length s = sep))⌝ ∗
        s_ptr ↦ s ∗ n_ptr ↦ W64 (sep.length : Int) ∗ sep_ptr ↦ sep)) at
        (if: #(decide _) then _ else #false) with [s n sep]
    · wp_if_destruct
      · try wp_auto
        rw [ite_eq_left (by word)]
        rw [show sint.nat (W64 (sep.length : Int)) - 0 = sep.length by word, List.drop_zero]
        try wp_auto
        iframe
        ipureintro
        rfl
      · iframe
        ipureintro
        rw [decide_eq_false (fun h => Hif (by rw [h]))]
    iintro ⟨%Hv, s, n, sep⟩
    subst Hv
    try wp_auto
    wp_if_destruct
    · -- found at 0
      try wp_auto
      rw [internal.bytealg.index_eq_of s sep 0 (by
        simp only [List.drop_zero]; exact List.prefix_iff_eq_take.2 Hif.symm) (by simp)]
      iapply HΦ
      itrivial
    try wp_auto
    have Hn : 0 < sep.length := by
      rcases Nat.eq_zero_or_pos sep.length with h | h
      · exact absurd (by rw [h, List.take_zero, eq_comm, ← List.length_eq_zero_iff, h]) Hif
      · exact h
    ihave HJ : (∃ (t : Nat), "i" ∷ i_ptr ↦ W64 ((t + sep.length : Nat) : Int) ∗
        "h" ∷ h_ptr ↦ internal.bytealg.hashStr ((s.drop t).take sep.length) ∗
        "%Ht" ∷ ⌜t + sep.length ≤ s.length ∧ ∀ k ≤ t, ¬ sep <+: s.drop k⌝ : IProp GF) $$ [i h]
    · iexists 0
      simp only [Nat.zero_add, List.drop_zero]
      iframe
      ipureintro
      refine ⟨Hle, fun k hk => ?_⟩
      rw [Nat.le_zero.1 hk, List.drop_zero]
      exact fun hp => Hif (List.prefix_iff_eq_take.1 hp).symm
    wp_for HJ
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hsl
    wp_if_destruct
    · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
      have Hlt : t + sep.length < s.length := by have := Ht.1; revert Hif; word
      obtain ⟨y, Hy⟩ : ∃ y, s[t + sep.length]? = some y := ⟨_, List.getElem?_eq_getElem Hlt⟩
      obtain ⟨x, Hx⟩ : ∃ x, s[t]? = some x := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      try wp_auto
      simp only [show sint.nat (W64 ((t + sep.length : Nat) : Int)) = t + sep.length by word,
        show 0 ≤ sint.Z (W64 ((t + sep.length : Nat) : Int)) by word, ↓reduceIte, Hy]
      try wp_auto
      rw [show W64 ((t + sep.length : Nat) : Int) - W64 (sep.length : Int) = W64 (t : Int) by word]
      simp only [show sint.nat (W64 (t : Int)) = t by word,
        show 0 ≤ sint.Z (W64 (t : Int)) by word, ↓reduceIte, Hx]
      try wp_auto
      rw [internal.bytealg.hashStr_window_roll s sep.length t x y Hn Hx Hy]
      rw [show W64 ((t + sep.length : Nat) : Int) + W64 1 = W64 ((t + 1 + sep.length : Nat) : Int)
        by word]
      have Hsub : W64 ((t + 1 + sep.length : Nat) : Int) - W64 (sep.length : Int) =
          W64 ((t + 1 : Nat) : Int) := by word
      wp_join (Q := fun v => iprop(
          ⌜v = #(decide (List.take sep.length (List.drop (t + 1) s) = sep))⌝ ∗
          s_ptr ↦ s ∗ n_ptr ↦ W64 (sep.length : Int) ∗ sep_ptr ↦ sep ∗
          i_ptr ↦ W64 ((t + 1 + sep.length : Nat) : Int))) at
          (if: #(decide _) then _ else #false) with [s n sep i]
      · wp_if_destruct
        · try wp_auto
          rw [Hsub, ite_eq_left (by word)]
          rw [show sint.nat (W64 ((t + 1 + sep.length : Nat) : Int)) -
              sint.nat (W64 ((t + 1 : Nat) : Int)) = sep.length by word,
            show sint.nat (W64 ((t + 1 : Nat) : Int)) = t + 1 by word]
          try wp_auto
          iframe
          ipureintro
          rfl
        · iframe
          ipureintro
          rw [decide_eq_false (fun h => Hif (by rw [h]))]
      iintro ⟨%Hv, s, n, sep, i⟩
      subst Hv
      try wp_auto
      wp_if_destruct
      · -- found at `t + 1`
        try wp_auto
        rw [Hsub]
        try wp_auto
        wp_for_post
        rw [internal.bytealg.index_eq_of s sep (t + 1)
          (List.prefix_iff_eq_take.2 Hif.symm) (fun k hk => Ht.2 k (by omega))]
        iapply HΦ
        itrivial
      · try wp_auto
        wp_for_post
        iframe
        iexists t + 1
        rw [show t + 1 + sep.length = t + 1 + sep.length from rfl]
        iframe
        ipureintro
        refine ⟨by omega, fun k hk => ?_⟩
        rcases Nat.lt_or_ge k (t + 1) with hk' | hk'
        · exact Ht.2 k (by omega)
        · rw [show k = t + 1 by omega]
          exact fun hp => Hif (List.prefix_iff_eq_take.1 hp).symm
    · try simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
      have Hge : t + sep.length = s.length := by have := Ht.1; revert Hif; word
      simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      rw [internal.bytealg.index_eq_neg s sep (fun k hk => by
        rcases Nat.lt_or_ge t k with hk' | hk'
        · have := hk.length_le; simp only [List.length_drop] at this; omega
        · exact Ht.2 k hk' hk)]
      iapply HΦ
      itrivial

end proof

end Perennial
