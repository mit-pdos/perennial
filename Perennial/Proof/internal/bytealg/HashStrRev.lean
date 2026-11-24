/-
The proof of `internal.bytealg.HashStrRev` (at `string`).
-/
module

public import Perennial.Spec.internal.bytealg.HashStrRev
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

theorem internal.bytealg.HashStrRev.wp_proof :
    internal.bytealg.HashStrRev.spec (GF := GF) (hG := hG) := by
  intro sep
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 ((j : Int) - 1) ∗
      "hash" ∷ hash_ptr ↦ internal.bytealg.hashStrRev (sep.drop j) ∗
      "%Hj" ∷ ⌜j ≤ sep.length⌝ : IProp GF) $$ [i hash]
  · iexists sep.length
    isplitl [i]
    · rw [show W64 ((sep.length : Int) - 1) = W64 (sep.length : Int) - W64 1 by word]
      iexact i
    isplitl [hash]
    · rw [show internal.bytealg.hashStrRev (List.drop sep.length sep) = W32 0 by
        simp [internal.bytealg.hashStrRev, internal.bytealg.hashStr, W32]]
      iexact hash
    ipureintro; exact Nat.le_refl _
  wp_for HI
  wp_if_destruct
  · rcases j with _ | k
    · exfalso; revert Hif; word
    have Hk : sint.nat (W64 (((k + 1 : Nat) : Int) - 1)) = k := by word
    have Hk0 : 0 ≤ sint.Z (W64 (((k + 1 : Nat) : Int) - 1)) := by word
    have Hlt : k < sep.length := by omega
    obtain ⟨b, Hb⟩ : ∃ b, sep[k]? = some b := ⟨_, List.getElem?_eq_getElem Hlt⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_for_post
    iframe
    iexists k
    isplitl [i]
    · rw [show W64 ((k : Int) - 1) = W64 (((k + 1 : Nat) : Int) - 1) - W64 1 by word]
      iexact i
    isplitl [hash]
    · rw [show sep.drop k = b :: sep.drop (k + 1) by
          rw [List.drop_eq_getElem_cons Hlt]; simp [List.getElem?_eq_getElem Hlt] at Hb; rw [Hb],
        internal.bytealg.hashStrRev_cons]
      iexact hash
    ipureintro; omega
  · rcases j with _ | k
    · simp only [List.drop_zero]
      try wp_auto
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

    · exfalso; apply Hif
      have := Hj
      word

end proof

end Perennial
