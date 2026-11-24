/-
The proof of `unicode.utf8.RuneCount`.
-/
module

public import Perennial.Spec.unicode.utf8.RuneCount

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : unicode.utf8.Assumptions]

theorem unicode.utf8.RuneCount.wp_proof : unicode.utf8.RuneCount.spec (GF := GF) (hG := hG) :=
    fun sl ys q Hascii => by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  ihave IH : iprop(∃ (i : w64),
      "n" ∷ n_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ (ys.length : Int)⌝) $$ [n]
  · iexists (W64 0)
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z i).toNat < ys.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, ys[(sint.Z i).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    rw [ite_eq_left ⟨Hi.1, Hif⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) ys q x Hi.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    have Hxa : uint.Z x < 128 := Hascii x (List.mem_of_getElem? Hx)
    wp_if_destruct
    · exfalso; word
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · have Hieq : i = W64 (ys.length : Int) := by word
    subst Hieq
    iapply HΦ
    iexact Hs

end proof

end Perennial
