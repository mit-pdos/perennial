/-
The proof of `slices.IndexFunc`.
-/
module

public import Perennial.Spec.slices.IndexFunc

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : slices.Assumptions]

theorem slices.IndexFunc.wp_proof :
    slices.IndexFunc.spec (GF := GF) (hG := hG) := by
  intro V _ _ Et _ S _ s dq xs f P
  wp_start as ⟨Hs, #Hf⟩
  iunfold slices.funcAnswers at Hf
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  rename_i k_ptr
  irename : (k_ptr ↦ zero_val w64 : IProp GF) => k
  ihave IH : iprop(∃ (n kv : w64),
      "i" ∷ i_ptr ↦ n ∗
      "k" ∷ k_ptr ↦ kv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z s.len⌝ ∗
      "%Hpre" ∷ ⌜∀ (j : Nat) (y : V), j < (sint.Z n).toNat → xs[j]? = some y → P y false⌝) $$ [i k]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨⟨by word, by word⟩, ?_⟩
    intro j y hj _
    simp at hj
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hmem : x ∈ xs := List.mem_of_getElem? Hx
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z n) xs dq x Hn.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len from ⟨Hn.1, Hif⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index s (sint.Z n) xs dq x Hn.1 $$ [Hs] with Hs
    · iframe; ipureintro; exact Hx
    ihave Hfx := Hf $$ %x %Hmem
    wp_apply Hfx as %b %Hb
    cases b
    · wp_auto
      wp_for_post
      iframe
      iexists _, _
      iframe
      ipureintro
      refine ⟨⟨by word, by word⟩, ?_⟩
      intro j y hj hy
      by_cases hjn : j < (sint.Z n).toNat
      · exact Hpre j y hjn hy
      · have : j = (sint.Z n).toNat := by word
        subst this
        rw [Hx] at hy
        cases hy
        exact Hb
    · wp_auto
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      right
      exact ⟨Hn.1, x, Hx, Hb, Hpre⟩
  · iapply HΦ
    iframe
    ipureintro
    left
    refine ⟨by word, ?_⟩
    intro x hx
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
    exact Hpre j x (by word) (by rw [List.getElem?_eq_getElem hj, hjx])

end proof

end Perennial
