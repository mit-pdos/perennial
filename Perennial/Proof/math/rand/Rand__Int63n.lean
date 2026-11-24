/-
The proof of `math/rand.Rand.Int63n`.
-/
module

public import Perennial.Spec.math.rand.Rand__Int63n
public import Perennial.Spec.math.rand.Rand__Int63

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : math.rand.Assumptions]

theorem math.rand.Rand.Int63n.wp_proof
    (wp_Int63 : math.rand.Rand.Int63.spec (GF := GF) (hG := hG)) :
    math.rand.Rand.Int63n.spec (GF := GF) (hG := hG) := by
  intro r n
  wp_start as ⟨#Hr, %Hn⟩
  wp_auto
  wp_if_destruct
  · exfalso; word
  wp_if_destruct
  · wp_apply wp_Int63 $$ Hr as %x %Hx
    iapply HΦ
    ipureintro
    have hm : sint.Z (n - W64 1) = sint.Z n - 1 := by word
    have := math.rand.and_toInt_bounds x (n - W64 1) (by word)
    simp only [sint.Z] at hm this ⊢
    omega
  simp only [show ¬uint.Z n = 0 by word, ↓reduceIte]
  wp_auto
  wp_apply wp_Int63 $$ Hr as %x %Hx
  ihave IH : iprop(∃ (y : w64), "v" ∷ v_ptr ↦ y ∗ "%Hy" ∷ ⌜0 ≤ sint.Z y⌝) $$ [v]
  · iexists x; iframe; ipureintro; exact Hx
  wp_for IH
  wp_if_destruct
  · wp_apply wp_Int63 $$ Hr as %x' %Hx'
    try wp_auto
    wp_for_post
    iframe
    iexists x'; iframe; ipureintro; exact Hx'
  · simp only [show ¬sint.Z n = 0 by word, ↓reduceIte]
    wp_auto
    iapply HΦ
    ipureintro; exact math.rand.srem_bounds y n Hy Hn

end proof

end Perennial
