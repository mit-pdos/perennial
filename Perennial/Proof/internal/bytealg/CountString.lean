/-
The proof of `internal.bytealg.CountString`.
-/
module

public import Perennial.Spec.internal.bytealg.CountString
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

theorem internal.bytealg.CountString.wp_proof :
    internal.bytealg.CountString.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  try wp_auto
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "n" ∷ n_ptr ↦ W64 ((s.take j).count c : Int) ∗
      "%Hj" ∷ ⌜j ≤ s.length⌝ : IProp GF) $$ [i n]
  · iexists 0
    simp only [List.take_zero, List.count_nil, Int.natCast_zero]
    iframe i n
    ipureintro; exact Nat.zero_le _
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · -- `i < len(s)`
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j < s.length := by revert Hif; word
    have Hk : sint.nat (W64 (j : Int)) = j := by word
    have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    obtain ⟨b, Hb⟩ : ∃ b, s[j]? = some b := ⟨_, List.getElem?_eq_getElem Hjl⟩
    have Htake : s.take (j + 1) = s.take j ++ [b] := by
      rw [List.take_add_one, Hb]; rfl
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_if_destruct
    · -- `s[i] == c`
      subst Hif
      try wp_auto
      wp_for_post
      iframe
      iexists j + 1
      isplitl [i]
      · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
        iexact i
      isplitl [n]
      · rw [Htake, List.count_append, List.count_singleton_self,
          show W64 ((((s.take j).count b + 1 : Nat)) : Int) =
            W64 (((s.take j).count b : Nat) : Int) + W64 1 by word]
        iexact n
      ipureintro; omega
    · try wp_auto
      wp_for_post
      iframe
      iexists j + 1
      isplitl [i]
      · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
        iexact i
      isplitl [n]
      · rw [Htake, List.count_append, List.count_singleton, ite_eq_right (by simpa using Hif)]
        iexact n
      ipureintro; omega
  · -- `i = len(s)`
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j = s.length := by revert Hif; word
    simp only [Hif, decide_false]
    subst Hjl
    try wp_auto
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [List.take_length]
    iapply HΦ
    ipureintro
    exact Hl

end proof

end Perennial
