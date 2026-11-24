/-
The proof of `strings.trimLeftASCII`.
-/
module

public import Perennial.Spec.strings.trimLeftASCII
public import Perennial.Spec.strings.asciiSet__contains
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
variable [package_sem : strings.Assumptions]

theorem strings.trimLeftASCII.wp_proof
    (wp_contains : strings.asciiSet.contains.spec (GF := GF) (hG := hG)) :
    strings.trimLeftASCII.spec (GF := GF) (hG := hG) := by
  intro s aset v dq
  wp_start as Has
  wp_auto
  irename «as» => Hasp
  ihave HI : (∃ (s' : GoString), "s" ∷ s_ptr ↦ s' ∗
      "%Hs" ∷ ⌜s.dropWhile (strings.asciiSetHas v) = s'.dropWhile (strings.asciiSetHas v)⌝ :
      IProp GF) $$ [s]
  · iexists s; iframe; ipureintro; rfl
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    obtain ⟨b, t, rfl⟩ : ∃ b t, s' = b :: t := by
      match s', Hif with
      | b :: t, _ => exact ⟨b, t, rfl⟩
      | [], h => exfalso; revert h; simp
    try wp_auto
    wp_apply wp_contains $$ Has as Has
    by_cases hb : strings.asciiSetHas v b = true
    · rw [hb]
      try wp_auto
      wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %-
      try wp_auto
      rw [ite_eq_left (by word)]
      rw [show sint.nat (W64 ((b :: t).length : Int)) = t.length + 1 by
        simp only [List.length_cons] at Hl ⊢; word]
      simp only [List.drop_one, List.tail_cons, Nat.add_sub_cancel, List.take_length]
      try wp_auto
      wp_for_post
      iframe
      iexists t
      iframe
      ipureintro
      rw [Hs, List.dropWhile_cons_of_pos hb]
    · rw [Bool.eq_false_iff.2 hb]
      try wp_auto
      wp_for_post
      try wp_auto
      rw [Hs, List.dropWhile_cons_of_neg hb]
      iapply HΦ
      iframe
  · simp only [intoVal_eq_iff, decide_eq_true_eq] at Hif
    have Hnil : s' = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
    subst Hnil
    simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    rw [Hs, List.dropWhile_nil]
    iapply HΦ
    iframe

end proof

end Perennial
