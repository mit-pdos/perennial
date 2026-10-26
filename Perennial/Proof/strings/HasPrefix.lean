/-
The proof of `strings.HasPrefix`.
-/
module

public import Perennial.Spec.strings.HasPrefix
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

/-- Proved from the model of `HasPrefix` (`Perennial/TrustedCode/strings.lean`). -/
theorem strings.HasPrefix.wp_proof :
    strings.HasPrefix.spec (GF := GF) (hG := hG) := by
  intro s pfx
  wp_start
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hs
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %Hp
  wp_if_destruct
  · rw [decide_eq_false (fun h => by have := h.length_le; word)]
    iapply HΦ; itrivial
  ihave IH : iprop(∃ n : w64,
      "i" ∷ i_ptr ↦ n ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (pfx.length : Int)⌝ ∗
      "%Heq" ∷ ⌜pfx.take (sint.nat n) = s.take (sint.nat n)⌝) $$ [i]
  · iexists _
    iframe
    ipureintro
    rw [show zero_val w64 = W64 0 from rfl]
    exact ⟨⟨by word, by word⟩, by simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero]⟩
  -- the Go variable `prefix` is a keyword in cases patterns
  irename «prefix» => Hpfx
  wp_for IH
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len with %-
  wp_if_destruct
  · have Hif' := of_decide_eq_true (go.intoVal_inj Hif)
    have Hlt : sint.nat n < pfx.length := by word
    have Hlt' : sint.nat n < s.length := by word
    rw [if_pos Hn.1, List.getElem?_eq_getElem Hlt']
    wp_auto
    rw [if_pos Hn.1, List.getElem?_eq_getElem Hlt]
    wp_auto
    wp_if_destruct
    · wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      rw [show sint.nat (n + W64 1) = sint.nat n + 1 by word, List.take_add_one,
        List.take_add_one, Heq, List.getElem?_eq_getElem Hlt', List.getElem?_eq_getElem Hlt, Hif]
    · wp_for_post
      rw [decide_eq_false]
      · iapply HΦ; itrivial
      intro h
      apply Hif
      obtain ⟨t, rfl⟩ := h
      simp [List.getElem_append_left Hlt]
  · have Hnot : ¬ sint.Z n < sint.Z (W64 pfx.length) := fun h => Hif (by rw [decide_eq_true h])
    simp only [decide_eq_false Hnot, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    rw [decide_eq_true]
    · iapply HΦ; itrivial
    rw [show sint.nat n = pfx.length by word, List.take_length] at Heq
    rw [Heq]
    exact List.take_prefix _ _

end proof

end Perennial
