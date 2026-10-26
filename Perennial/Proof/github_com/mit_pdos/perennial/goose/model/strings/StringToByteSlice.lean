/-
The proof of `StringToByteSlice` (`goose/model/strings/convert.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : go.StringSemantics]

theorem github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice.wp_proof : github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice.spec (GF := GF) (hG := hG) := by
  intro s E str
  wp_start
  wp_auto
  wp_apply wp_slice_make2 (V := w8) (t := go.byte) (W64 0) with %a0 ⟨Ha0, Ha0_cap⟩
  · ipureintro; word
  ihave H : (∃ (i : w64) (a : GoSlice),
      "i" ∷ i_ptr ↦ i ∗
      "a" ∷ a_ptr ↦ a ∗
      "Ha" ∷ a ↦* str.take (sint.nat i) ∗
      "Ha_cap" ∷ ownSliceCap w8 a (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ str.length⌝ : IProp GF) $$ [a i Ha0 Ha0_cap]
  · iexists (W64 0)
    iexists a0
    have h0 : str.take (sint.nat (W64 0)) = List.replicate 0 (zero_val w8) := by
      rw [show sint.nat (W64 0) = 0 from rfl]; rfl
    rw [h0]
    iframe a i Ha0 Ha0_cap
    ipureintro; word
  wp_for H
  wp_apply wp_string_len with %Hoverflow
  wp_if_destruct
  · have hlt : sint.Z i < sint.Z (W64 str.length) := by
      rcases Decidable.em (sint.Z i < sint.Z (W64 str.length)) with h | h
      · exact h
      · rw [decide_eq_false h] at Hif; exact absurd Hif false_neq_true
    have hc : sint.nat i < str.length := by word
    obtain ⟨c, Hc_lookup⟩ : ∃ c, str[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hc⟩
    simp only [Hi.1, ↓reduceIte, Hc_lookup]
    wp_pure
    wp_pure
    wp_pure
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte)))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [c]
    wp_auto
    have hsz : go.arrayLiteralSize [KeyedElement none (ElementExpression go.byte #c)] = 1 := rfl
    rw [hsz]
    isplitl []
    · ipureintro; rfl
    iintro %sl_ptr ⟨Hsl, _⟩
    wp_auto
    wp_apply wp_slice_append (V := w8) (t := go.byte) a _ _ [c] (DFrac.own 1) $$ [Ha Ha_cap Hsl]
      with %s' ⟨Ha, Ha_cap, _⟩
    · iframe Ha Ha_cap Hsl
    wp_for_post
    iframe
    iexists (i + W64 1)
    iexists s'
    have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hn, List.take_add_one, Hc_lookup]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hP : ¬ sint.Z i < sint.Z (W64 str.length) := fun h => Hif (by rw [decide_eq_true h])
    rw [decide_eq_false hP]
    simp only [Bool.false_eq_true, decide_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    have hi : sint.nat i = str.length := by word
    rw [hi, List.take_length]
    iframe Ha Ha_cap

end proof

end Perennial
