/-
The proof of `rangeMapLabeled` (a goose semantics test, `labels.go`).
-/
module

public import Perennial.Spec.github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled

/-- What the loop adds for key `k`: the keys whose value is odd (all but `2`). -/
def f (k : w64) : w64 := if k = W64 2 then 0 else k

/-- The sum of `f` over `l`. -/
def fsum : List w64 → w64
  | [] => 0
  | k :: l => f k + fsum l

theorem fsum_append (l : List w64) (k : w64) : fsum (l ++ [k]) = fsum l + f k := by
  induction l with
  | nil => simp [fsum]
  | cons a l ih => simp only [List.cons_append, fsum, ih]; word

theorem fsum_perm {l l' : List w64} (h : l.Perm l') : fsum l = fsum l' := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [fsum, ih]
  | swap x y l => simp only [fsum]; word
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.semantics.Assumptions]
open github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled

theorem github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled.wp_proof :
    github_com.mit_pdos.perennial.goose.testdata.examples.semantics.rangeMapLabeled.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64)) with %m Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply wp_mapInsert $$ Hm with Hm
  wp_apply (wp_map_for_range (fun keys i => iprop(
      "sum" ∷ sum_ptr ↦ fsum (keys.take i.toNat) ∗ "HΦ" ∷ (True -∗ Φ #(W64 4)) ∗
      "«$res0»" ∷ «$res0_ptr» ↦ W64 0 ∗
      "k" ∷ (∃ kv : w64, k_ptr ↦ kv) ∗ "v" ∷ (∃ vv : w64, v_ptr ↦ vv) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝))) $$ Hm
  iintro %keys ⟨%Hmem, %Hsize, %Hnd⟩
  isplitl [sum HΦ «$res0» k v]
  · iframe
    isplitl [k]
    · iexists _; iframe
    isplitl [v]
    · iexists _; iframe
    ipureintro; omega
  isplitr
  · imodintro
    iintro %i %key %vl ⟨%Hk, %Hlook⟩ ⟨sum, HΦ, «$res0», ⟨%kv, k⟩, ⟨%vv, v⟩, %Hi⟩
    have htake : keys.take (i + 1).toNat = keys.take i.toNat ++ [key] := by
      rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, Hk]; rfl
    simp only [GMap.lookup_insert_eq_iff] at Hlook
    have hcase : (key = W64 3 ∧ vl = W64 33) ∨ (key = W64 2 ∧ vl = W64 22) ∨
        (key = W64 1 ∧ vl = W64 11) := by
      split at Hlook
      · next h => exact .inl ⟨by subst h; rfl, (Option.some.inj Hlook).symm⟩
      split at Hlook
      · next h => exact .inr (.inl ⟨by subst h; rfl, (Option.some.inj Hlook).symm⟩)
      split at Hlook
      · next h => exact .inr (.inr ⟨by subst h; rfl, (Option.some.inj Hlook).symm⟩)
      · simp at Hlook
    rw [htake, fsum_append]
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · wp_auto
      ihave HJ : (True : IProp GF) $$ []
      · itrivial
      wp_for HJ
      wp_for_post
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
    · wp_auto
      ihave HJ : (True : IProp GF) $$ []
      · itrivial
      wp_for HJ
      wp_for_post
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      rw [show f (W64 2) = 0 from rfl, show ∀ x : w64, x + 0 = x by intro; word]
      iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
    · wp_auto
      ihave HJ : (True : IProp GF) $$ []
      · itrivial
      wp_for HJ
      wp_for_post
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iframe
      isplitl [k]
      · iexists _; iframe
      isplitl [v]
      · iexists _; iframe
      ipureintro; omega
  · iintro ⟨sum, HΦ, «$res0», k, v, %Hi⟩ Hm
    have hperm : keys.Perm [W64 1, W64 2, W64 3] := by
      rw [List.perm_ext_iff_of_nodup Hnd (by decide)]
      intro a
      rw [Hmem a]
      by_cases h3 : W64 3 = a <;> by_cases h2 : W64 2 = a <;> by_cases h1 : W64 1 = a <;>
        simp_all <;> grind
    simp only [Int.toNat_natCast, ← Hsize]
    rw [List.take_of_length_le (Nat.le_refl _), fsum_perm hperm]
    wp_auto
    rw [show fsum [W64 1, W64 2, W64 3] = W64 4 by simp only [fsum, f]; decide]
    iapply HΦ
    itrivial

end proof

end Perennial
