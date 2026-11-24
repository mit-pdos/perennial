/-
The proof of `internal.bytealg.HashStr` (at `string`).
-/
module

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

theorem internal.bytealg.HashStr.wp_proof :
    internal.bytealg.HashStr.spec (GF := GF) (hG := hG) := by
  intro sep
  wp_start
  wp_auto
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "hash" ∷ hash_ptr ↦ internal.bytealg.hashStr (sep.take j) ∗
      "%Hj" ∷ ⌜j ≤ sep.length⌝ : IProp GF) $$ [i hash]
  · iexists 0
    iframe i
    isplitl
    · rw [show internal.bytealg.hashStr (List.take 0 sep) = W32 0 by simp [internal.bytealg.hashStr, W32]]
      iexact hash
    ipureintro; exact Nat.zero_le _
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j < sep.length := by have := Hj; revert Hif; word
    have Hk : sint.nat (W64 (j : Int)) = j := by word
    have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    obtain ⟨b, Hb⟩ : ∃ b, sep[j]? = some b := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_for_post
    iframe
    iexists j + 1
    isplitl [i]
    · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
      iexact i
    isplitl [hash]
    · rw [List.take_add_one, Hb, Option.toList_some, internal.bytealg.hashStr_append_singleton]
      iexact hash
    ipureintro; omega
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j = sep.length := by have := Hj; revert Hif; word
    simp only [Hif, decide_false]
    try wp_auto
    subst Hjl
    rw [List.take_length]
    try simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    ihave HJ : (∃ (k : Nat) (p q : w32), "i" ∷ i_ptr ↦ W64 (k : Int) ∗
        "pow" ∷ pow_ptr ↦ p ∗ "sq" ∷ sq_ptr ↦ q ∗
        "%Hk" ∷ ⌜k ≤ sep.length ∧ p * q ^ k = internal.bytealg.powRK sep.length⌝ : IProp GF)
        $$ [i pow sq]
    · iexists sep.length, W32 1, W32 16777619
      iframe
      ipureintro
      refine ⟨Nat.le_refl _, ?_⟩
      rw [internal.bytealg.powRK_eq_pow]
      simp [internal.bytealg.primeRK]
    wp_for HJ
    wp_if_destruct
    · have Hk0 : 0 < k := by have := Hk.1; revert Hif; word
      try wp_auto
      wp_if_destruct
      · have Hev : k % 2 = 0 := (internal.bytealg.and_one_eq_zero_nat k (by omega)).1 Hif
        try wp_auto
        wp_for_post
        try wp_auto
        rw [internal.bytealg.sshiftRight'_one_nat k (by omega)]
        iframe
        iexists k / 2, p, q * q
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        rw [← Hk.2, internal.bytealg.pow_halve q k, Hev]
        simp
      · have Hodd : k % 2 = 1 := by
          rcases Nat.mod_two_eq_zero_or_one k with h | h
          · exact absurd ((internal.bytealg.and_one_eq_zero_nat k (by omega)).2 h) Hif
          · exact h
        try wp_auto
        wp_for_post
        try wp_auto
        rw [internal.bytealg.sshiftRight'_one_nat k (by omega)]
        iframe
        iexists k / 2, p * q, q * q
        iframe
        ipureintro
        refine ⟨by omega, ?_⟩
        rw [← Hk.2, internal.bytealg.pow_halve q k, Hodd]
        simp only [↓reduceIte]
        grind
    · have Hk0 : k = 0 := by have := Hk.1; revert Hif; word
      subst Hk0
      try wp_auto
      rw [show p = internal.bytealg.powRK sep.length by simpa using Hk.2]
      iapply HΦ
      itrivial

end proof

end Perennial
