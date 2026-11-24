/-
The proof of `strings.trimLeftByte`.
-/
module

public import Perennial.Spec.strings.trimLeftByte

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

theorem strings.trimLeftByte.wp_proof :
    strings.trimLeftByte.spec (GF := GF) (hG := hG) := by
  intro s c
  wp_start
  wp_auto
  ihave HI : (∃ (s' : GoString), "s" ∷ s_ptr ↦ s' ∗
      "%Hs" ∷ ⌜s.dropWhile (fun b => decide (b = c)) = s'.dropWhile (fun b => decide (b = c))⌝ :
      IProp GF) $$ [s]
  · iexists s; iframe; ipureintro; rfl
  wp_for HI
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hl
  wp_if_destruct
  · obtain ⟨b, t, rfl⟩ : ∃ b t, s' = b :: t := by
      match s', Hif with
      | b :: t, _ => exact ⟨b, t, rfl⟩
      | [], h => exfalso; revert h; simp
    try wp_auto
    rw [if_decide_bool_eq_true]
    by_cases hbc : b = c
    · subst hbc
      simp only [decide_true, ↓reduceIte]
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
      rw [Hs, List.dropWhile_cons_of_pos (by simp)]
    · simp only [hbc, decide_false, Bool.false_eq_true, ↓reduceIte]
      try simp only [_root_.decide_true, ↓reduceIte]
      try wp_auto
      rw [Hs, List.dropWhile_cons_of_neg (by simpa using hbc)]
      iapply HΦ
      itrivial
  · have Hnil : s' = [] := List.eq_nil_of_length_eq_zero (by revert Hif; word)
    subst Hnil
    rw [Hs, List.dropWhile_nil]
    iapply HΦ
    itrivial

end proof

end Perennial
