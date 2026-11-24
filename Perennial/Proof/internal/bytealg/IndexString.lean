/-
The proof of `internal.bytealg.IndexString` (its Go model,
`goose/model/overlay/internal/bytealg/index_native.go`).
-/
module

public import Perennial.Spec.internal.bytealg.IndexString
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

theorem internal.bytealg.IndexString.wp_proof :
    internal.bytealg.IndexString.spec (GF := GF) (hG := hG) := by
  intro a b m
  wp_start as ⟨#HMaxLen, %Hb⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hbl
  wp_if_destruct
  · exfalso; revert Hif; word
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · exfalso; revert Hif; word
  try wp_auto
  ihave HI : (∃ (j : Nat), "i" ∷ i_ptr ↦ W64 (j : Int) ∗
      "%Hj" ∷ ⌜j ≤ a.length - b.length + 1 ∧ ∀ k < j, ¬ b <+: a.drop k⌝ : IProp GF)
      $$ [i]
  · iexists 0
    iframe i
    ipureintro
    refine ⟨by omega, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hal
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
  wp_if_destruct
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjb : j + b.length ≤ a.length := by have := Hj.1; revert Hif; word
    wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
    try wp_auto
    rw [ite_eq_left (by word)]
    rw [show sint.nat (W64 (j : Int) + W64 (b.length : Int)) - sint.nat (W64 (j : Int)) = b.length
      by word, show sint.nat (W64 (j : Int)) = j by word]
    try wp_auto
    wp_if_destruct
    · -- found
      try wp_auto
      wp_for_post
      rw [internal.bytealg.index_eq_of a b j (List.prefix_iff_eq_take.2 Hif.symm) Hj.2]
      iapply HΦ
      itrivial
    · try wp_auto
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
      · intro hp; exact ‹¬_› (List.prefix_iff_eq_take.1 hp).symm
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hjb : a.length < j + b.length := by have := Hj.1; revert Hif; word
    simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [internal.bytealg.index_eq_neg a b (fun k hk => by
      rcases Nat.lt_or_ge k j with hkj | hkj
      · exact Hj.2 k hkj hk
      · have := hk.length_le; simp only [List.length_drop] at this; omega)]
    iapply HΦ
    itrivial

end proof

end Perennial
