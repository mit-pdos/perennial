/-
The proof of `internal.bytealg.IndexByteString`.
-/
module

public import Perennial.Spec.internal.bytealg.IndexByteString
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

theorem internal.bytealg.IndexByteString.wp_proof :
    internal.bytealg.IndexByteString.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  try wp_auto
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "%Hj" ∷ ⌜j ≤ s.length ∧ ∀ k < j, s[k]? ≠ some c⌝ : IProp GF) $$ [i]
  · iexists 0
    iframe i
    ipureintro; exact ⟨Nat.zero_le _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · -- `i < len(s)`
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j < s.length := by have := Hj.1; clear Hj; revert Hif; word
    have Hk : sint.nat (W64 (j : Int)) = j := by clear Hj; word
    have Hk0 : 0 ≤ sint.Z (W64 (j : Int)) := by clear Hj; word
    obtain ⟨b, Hb⟩ : ∃ b, s[j]? = some b := ⟨_, List.getElem?_eq_getElem Hjl⟩
    try wp_auto
    simp only [Hk, Hk0, ↓reduceIte, Hb]
    try wp_auto
    wp_if_destruct
    · -- found
      try wp_auto
      wp_for_post
      subst Hif
      rw [internal.bytealg.indexByte_eq_of s b j Hb Hj.2]
      iapply HΦ
      ipureintro
      exact Hl
    ·
      try wp_auto
      wp_for_post
      iframe
      iexists j + 1
      isplitl
      · rw [show W64 (((j + 1 : Nat) : Int)) = W64 (j : Int) + W64 1 by word]
        iexact i
      ipureintro
      refine ⟨by omega, fun k hk => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact Hj.2 k hk
      · rw [Hb]; intro h; exact ‹¬b = c› (Option.some.inj h)
  · -- `i = len(s)`
    simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjl : j = s.length := by have := Hj.1; clear Hj; revert Hif; word
    simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [internal.bytealg.indexByte_eq_neg s c (fun k => by
      rcases Nat.lt_or_ge k s.length with hk | hk
      · exact Hj.2 k (by omega)
      · simp [List.getElem?_eq_none hk])]
    iapply HΦ
    ipureintro
    exact Hl

end proof

end Perennial
