/-
The proof of `sort.Find`.
-/
module

public import Perennial.Spec.sort.Find
public import Perennial.Proof.sort.FindBasics

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

theorem sort.Find.wp_proof : sort.Find.spec (GF := GF) (hG := hG) := fun n cmp_code cmp I => by
  -- (`fun`, not `intro`: `wp_apply_post` runs `whnfR` outside the goal's context, so a
  -- `wp_apply` fails silently on binders introduced by a tactic)
  wp_start as ⟨%Hpos, #Hcmp0, I, %Hvalid⟩
  wp_auto
  ihave #Hcmp := cmpImplements_adapt cmp_code cmp (sint.Z n) I $$ Hcmp0
  iclear Hcmp0
  have Hvalid := isValidCmp_adapted cmp (sint.Z n) Hpos Hvalid
  obtain ⟨Hmono, Hneg, Hn⟩ := Hvalid
  unfold cmpImplements
  ihave HI : (∃ (i j : w64),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "I" ∷ I ∗
      "%Hbounds" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z j ∧ sint.Z j ≤ sint.Z n⌝ ∗
      "%Hi_prop" ∷ ⌜adaptCmp cmp (sint.Z n) (sint.Z i - 1) > 0⌝ ∗
      "%Hj_prop" ∷ ⌜adaptCmp cmp (sint.Z n) (sint.Z j) ≤ 0⌝ : IProp GF) $$ [i j I]
  · iexists _, _
    iframe
    ipureintro
    refine ⟨by word, ?_, Hn⟩
    rw [show sint.Z (W64 0) - 1 = -1 by decide, Hneg]; decide
  wp_for HI
  wp_if_destruct
  · have Hj : sint.Z i ≤ sint.Z ((i + j) >>> W64 1) ∧ sint.Z ((i + j) >>> W64 1) < sint.Z j := by
      rw [shiftr_1_eq_div]; word'
    wp_apply Hcmp $$ [I] with %r ⟨I, %Hcmp_result⟩
    · iframe I; ipureintro; omega
    generalize (i + j) >>> W64 1 = h at Hj Hcmp_result ⊢
    wp_if_destruct
    · -- cmp(h) > 0, so i = h + 1
      wp_for_post
      iframe
      iexists (h + W64 1), j
      iframe
      ipureintro
      refine ⟨by word, ?_, Hj_prop⟩
      have : sint.Z (h + W64 1) - 1 = sint.Z h := by word
      rw [this, ← Hcmp_result]; word
    · -- cmp(h) ≤ 0, so j = h
      wp_for_post
      iframe
      iexists i, h
      iframe
      ipureintro
      refine ⟨by word, Hi_prop, ?_⟩
      rw [← Hcmp_result]; word
  · have Hij : sint.Z i = sint.Z j := by omega
    wp_if_destruct
    · wp_apply Hcmp $$ [I] with %r ⟨I, %Hr⟩
      · iframe I; ipureintro; omega
      iapply HΦ
      iframe I
      ipureintro
      rw [adaptCmp_bounded _ _ _ (by omega)] at Hr
      refine ⟨?_, ?_, find_prefix cmp _ _ Hmono (by omega) Hi_prop⟩
      · rw [decide_eq_true_iff]
        constructor
        · intro h; subst h; refine ⟨Hif, ?_⟩; rw [← Hr]; decide
        · intro ⟨_, h⟩; rw [h] at Hr; word
      · intro H
        have := H (sint.Z i) (by omega)
        rw [← Hij, adaptCmp_bounded _ _ _ (by omega)] at Hj_prop
        omega
    · iapply HΦ
      iframe I
      ipureintro
      refine ⟨by simp only [Bool.false_eq_true, false_iff]; omega, fun _ => by omega,
        find_prefix cmp _ _ Hmono (by omega) Hi_prop⟩

end proof

end Perennial
