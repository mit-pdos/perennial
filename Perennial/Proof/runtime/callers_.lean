/-
The proof of `runtime.callers` (its trusted model, `TrustedCode/runtime.lean`).
-/
module

public import Perennial.Spec.runtime.callers_

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : runtime.Assumptions]

theorem runtime.callers.wp_proof :
    runtime.callers.spec (GF := GF) (hG := hG) := fun skip s xs => by
  wp_start as Hs
  ihave %Hlen := ownSlice_len $$ Hs
  wp_auto
  ihave HI : iprop(∃ (n : w64) (ys : List w64),
      "n" ∷ n_ptr ↦ n ∗
      "Hs" ∷ s ↦* ys ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ xs.length ∧ ys.length = xs.length ∧
        ys.drop (sint.nat n) = xs.drop (sint.nat n)⌝) $$ [n Hs]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by decide, by simp, rfl, rfl⟩
  wp_for HI
  ihave %Hlen' := ownSlice_len $$ Hs
  wp_if_destruct
  · wp_apply wp_ArbitraryInt as %c -
    by_cases hc : c = W64 0
    · subst hc
      rw [show (!decide (W64 0 = W64 0)) = false from rfl]
      simp only [if_decide_false_eq_true]
      simp only [decide_eq_true_eq, ↓reduceIte]
      wp_auto
      iapply HΦ
      iexists ys
      iframe
      ipureintro; exact Hn
    · have Hf : (!decide (c = W64 0)) = true := by rw [decide_eq_false hc]; rfl
      rw [Hf]
      simp only [decide_eq_true_eq, ↓reduceIte]
      wp_apply wp_ArbitraryInt as %v -
      have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z s.len := ⟨Hn.1, Hif⟩
      have hsl : (ys.length : Int) = sint.Z s.len := by
        rw [Hlen'.1]; show ((sint.Z s.len).toNat : Int) = _; omega
      have hxl : (xs.length : Int) = sint.Z s.len := by
        rw [Hlen.1]; show ((sint.Z s.len).toNat : Int) = _; omega
      rw [ite_eq_left hb]
      wp_apply wp_store_slice_index s (sint.Z n) ys v $$ [Hs] as Hs
      · iframe; ipureintro; omega
      wp_for_post
      have hn1 : sint.Z (n + W64 1) = sint.Z n + 1 := by word
      have hk : sint.nat (n + W64 1) = sint.nat n + 1 := by
        show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1
        omega
      have hk' : (sint.nat (n + W64 1) : Int) = sint.Z n + 1 := by
        show ((sint.Z (n + W64 1)).toNat : Int) = _
        omega
      iframe
      iexists (n + W64 1), (ys.set (sint.Z n).toNat v)
      iframe
      ipureintro
      refine ⟨by omega, by omega, by simp [Hn.2.2.1], ?_⟩
      rw [hk, List.drop_set_of_lt (by show (sint.Z n).toNat < (sint.Z n).toNat + 1; omega),
        ← List.drop_drop, ← List.drop_drop, Hn.2.2.2]
  · iapply HΦ
    iexists ys
    iframe
    ipureintro; exact Hn

end proof

end Perennial
