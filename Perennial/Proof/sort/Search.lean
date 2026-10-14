/-
The proof of `sort.Search`.
-/
module

public import Perennial.Spec.sort.Search
public import Perennial.Proof.sort.SearchBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

theorem sort.Search.wp_proof : sort.Search.spec (GF := GF) (hG := hG) := fun n f_code f I => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as ⟨%Hpos, #Hf0, I, %Hvalid⟩
  wp_auto
  ihave #Hf := predImplements_adapt f_code f (sint.Z n) I $$ Hf0
  iclear Hf0
  have Hvalid := isValidPred_adapted f (sint.Z n) Hpos Hvalid
  obtain ⟨Hmono, Hneg, Hn⟩ := Hvalid
  unfold predImplements
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜adaptPred f (sint.Z n) (sint.Z i - 1) = false⌝ ∗
      "%Hj_prop" ∷ ⌜adaptPred f (sint.Z n) (sint.Z j) = true⌝ : IProp GF) $$ [i j I]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, Hn⟩
    rw [show sint.Z (W64 0) - 1 = -1 by decide, Hneg]
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [shiftr_1_eq_div]; word'
    wp_apply Hf $$ [I] with %r ⟨I, %Hf_result⟩
    · iframe I; ipureintro; omega
    generalize (i + j) >>> W64 1 = h at Hj Hf_result ⊢
    cases r
    · -- `!f(h)`, so `f(h) = false`, so `i = h + 1`
      simp only [Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists (h + W64 1), j
      iframe
      ipureintro
      refine ⟨by word, ?_, Hj_prop⟩
      have : sint.Z (h + W64 1) - 1 = sint.Z h := by word
      rw [this, ← Hf_result]
    · -- `f(h) = true`, so `j = h`
      simp only [Bool.not_true]
      wp_auto
      wp_for_post
      iframe
      iexists i, h
      iframe
      ipureintro
      exact ⟨by word, Hi_prop, Hf_result.symm⟩
  · -- loop exit: `i = j`
    have Hij : sint.Z i = sint.Z j := by omega
    iapply HΦ
    iframe I
    ipureintro
    refine ⟨by omega, ?_, ?_, ?_⟩
    · intro Hilt
      rw [← Hij, adaptPred_bounded _ _ _ (by omega)] at Hj_prop
      exact Hj_prop
    · intro Hno_true
      by_cases hlt : sint.Z i < sint.Z n
      · rw [← Hij, adaptPred_bounded _ _ _ (by omega)] at Hj_prop
        have := Hno_true (sint.Z i) (by omega)
        simp_all
      · omega
    · intro k Hk
      by_cases hk : k = sint.Z i - 1
      · subst hk; rwa [adaptPred_bounded _ _ _ (by omega)] at Hi_prop
      · cases hfk : f k
        · rfl
        · have := Hmono k (sint.Z i - 1) (by omega)
            (by rw [adaptPred_bounded _ _ _ (by omega)]; exact hfk)
          simp_all

end proof

end Perennial
