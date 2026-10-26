/-
The proof of `github.com/goose-lang/std/std_core.Permutation`.
-/
module

public import Perennial.Spec.github_com.goose_lang.std.std_core.Permutation
public import Perennial.Spec.github_com.goose_lang.std.std_core.Shuffle

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem_fn : GoSemanticsFunctions] [sem : go.PreSemantics]
variable [package_sem : github_com.goose_lang.std.std_core.Assumptions]

theorem github_com.goose_lang.std.std_core.Permutation.wp_proof
    (wp_Shuffle : github_com.goose_lang.std.std_core.Shuffle.spec (GF := GF) (hG := hG)) :
    github_com.goose_lang.std.std_core.Permutation.spec (GF := GF) (hG := hG) := fun n => by
  wp_start as %Hnz
  wp_auto
  wp_apply wp_slice_make2 (V := w64) n $$ [] as %s ⟨Hs, -⟩
  · ipureintro; exact Hnz
  have hnu := sint_eq_uint n Hnz
  simp only [show (zero_val w64 : w64) = W64 0 from rfl]
  ihave HI : (∃ (i : w64),
      "Hs" ∷ s ↦* (((seqZ 0 (sint.Z i)).map (fun z => W64 z)) ++
        List.replicate (sint.nat n - sint.nat i) (W64 0)) ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z n⌝ : IProp GF) $$ [i Hs]
  · iexists (W64 0)
    simp only [seqZ_nil 0 (sint.Z (W64 0)) (by decide), List.map_nil, List.nil_append,
      show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; exact ⟨by decide, Hnz⟩
  wp_for HI
  have hiu := sint_eq_uint i Hi.1
  by_cases Hif : uint.Z i < uint.Z n
  · simp only [Hif, _root_.decide_true, ↓reduceIte]
    wp_auto
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    have hlt : sint.nat i < sint.nat n := by simp only [sint.nat, sint.Z] at *; omega
    have hsl : sint.Z i < sint.Z s.len := by
      simp only [List.length_append, List.length_map, length_seqZ, List.length_replicate] at Hlen
      simp only [sint.nat, sint.Z] at *; omega
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, hsl⟩)]
    wp_pures
    wp_apply wp_store_slice_index s (sint.Z i) _ i $$ [Hs] with Hs
    · iframe Hs; ipureintro; simp [length_seqZ]; simp only [sint.nat, sint.Z] at *; omega
    wp_for_post
    iframe
    iexists (i + W64 1)
    have hi1 := sint_succ_of_lt i n Hif Hi.1 Hnz
    have hstep := perm_step (sint.nat i) (sint.nat n) hlt
    have e1 : ((sint.nat i : Nat) : Int) = sint.Z i := by simp only [sint.nat, sint.Z] at *; omega
    have e2 : sint.nat i + 1 = sint.nat (i + W64 1) := by simp only [sint.nat, sint.Z] at *; omega
    rw [e1, W64_sint, e2, ← hi1] at hstep
    rw [show (sint.Z i).toNat = sint.nat i from rfl, hstep]
    iframe
    ipureintro; omega
  · simp only [Hif, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_apply wp_Shuffle s _ $$ [$Hs] as %xs' ⟨%Hperm, Hs⟩
    iapply HΦ
    iframe Hs
    ipureintro
    have hin : i = n := by
      apply BitVec.eq_of_toNat_eq; simp only [uint.Z, sint.Z] at *; omega
    subst hin
    simp only [Nat.sub_self, List.replicate_zero, List.append_nil] at Hperm
    exact Hperm.symm

end proof

end Perennial
