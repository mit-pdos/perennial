/-
The proof of `ByteSliceToString` (`goose/model/strings/convert.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString

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

theorem github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString.wp_proof : github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString.spec (GF := GF) (hG := hG) := by
  intro s E sl str dq
  wp_start as Hsl
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  ihave H : (∃ (i : w64) (c : w8),
      "i" ∷ i_ptr ↦ i ∗
      "c" ∷ c_ptr ↦ c ∗
      "s" ∷ s_ptr ↦ str.take (sint.nat i) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ str.length⌝ : IProp GF) $$ [s c i]
  · iexists (W64 0)
    iexists (zero_val w8)
    have h0 : sint.nat (W64 0) = 0 := rfl
    rw [h0, List.take_zero]
    iframe
    ipureintro; word
  wp_for H
  wp_if_destruct
  · rw [ite_eq_left ⟨Hi.1, Hif⟩]
    have hc : sint.nat i < str.length := by word
    obtain ⟨c', Hc_lookup⟩ : ∃ c, str[sint.nat i]? = some c := ⟨_, List.getElem?_eq_getElem hc⟩
    wp_apply wp_load_slice_index (V := w8) (t := go.byte) sl (sint.Z i) str dq c' Hi.1 $$ [Hsl]
      with Hsl
    · isplitl [Hsl]
      · iexact Hsl
      · ipureintro; exact Hc_lookup
    generalize hL : (W8 0 :: _ : GoString) = L
    have hfacts : L.length = 256 ∧ ∀ c : w8, (L.drop (uint.nat c)).take 1 = [c] := by
      subst hL; decide +kernel
    have h1 : sint.Z (W64 (uint.Z c')) = uint.Z c' := by word
    have h2 : sint.Z (W64 (uint.Z c') + W64 1) = uint.Z c' + 1 := by word
    rw [ite_eq_left (by rw [h1, h2, hfacts.1]; word),
      show sint.nat (W64 (uint.Z c') + W64 1) - sint.nat (W64 (uint.Z c')) = 1 by word,
      show sint.nat (W64 (uint.Z c')) = uint.nat c' by word, hfacts.2]
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1)
    iexists c'
    have hn : sint.nat (i + W64 1) = sint.nat i + 1 := by word
    rw [hn, List.take_add_one, Hc_lookup]
    simp only [Option.toList_some]
    iframe
    ipureintro; word
  · have hi : sint.nat i = str.length := by word
    rw [hi, List.take_length]
    iapply HΦ $$ Hsl

end proof

end Perennial
