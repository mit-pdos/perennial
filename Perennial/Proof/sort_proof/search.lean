/-
Proofs of `sort.Search` and
`sort.SearchInts`.

The specification for `sort.Search` is simpler than `sort.Find`: it takes a
predicate function (`f : Int → Bool`) and a number `n`, and it searches for the
first `i ∈ [0, n)` such that `f i = true`, assuming `f` goes from false to true.
As for `Find`, `0 ≤ n` is a precondition, `f` is only called on `[0, n)`, and
the user-provided `f` is "adapted" (`adaptPred`) so that `f (-1) = false` and
`f n = true`.
-/
import Perennial.Proof.ProofPrelude
import Perennial.Code.sort
import Perennial.GeneratedProof.sort
import Perennial.Proof.sort_proof.sort_init
import Perennial.Proof.sort_proof.find

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace sort

/-- "proper" monotonicity on only `[0, n)` - a sensible precondition for `Search`. -/
def IsMonoPred (f : Int → Bool) (n : Int) : Prop :=
  ∀ i j, 0 ≤ i ∧ i < j ∧ j < n → f i = true → f j = true

def adaptPred (f : Int → Bool) (n : Int) : Int → Bool :=
  fun i => if i < 0 then false else
           if n ≤ i then true
           else f i

theorem adaptPred_bounded (f : Int → Bool) (n : Int) :
    ∀ i, 0 ≤ i ∧ i < n → adaptPred f n i = f i := by
  intro i H
  unfold adaptPred
  simp only [show ¬ i < 0 by omega, show ¬ n ≤ i by omega, ↓reduceIte]

/-- "internal" monotonicity on `[-1, n]` by extending (adapting) `f`. -/
def IsValidPred (f : Int → Bool) (n : Int) : Prop :=
  (∀ i j, -1 ≤ i ∧ i < j ∧ j ≤ n → f i = true → f j = true) ∧
  f (-1) = false ∧
  f n = true

theorem isValidPred_adapted (f : Int → Bool) (n : Int) :
    0 ≤ n → IsMonoPred f n → IsValidPred (adaptPred f n) n := by
  unfold IsMonoPred IsValidPred
  intro Hnn Hmono
  refine ⟨?_, ?_, ?_⟩
  · intro i j Hij Hfi
    by_cases h : 0 ≤ i ∧ j < n
    · rw [adaptPred_bounded _ _ i (by omega)] at Hfi
      rw [adaptPred_bounded _ _ j (by omega)]
      exact Hmono i j (by omega) Hfi
    · unfold adaptPred at Hfi ⊢
      (repeat' split) <;> (repeat' split at Hfi) <;> first | rfl | omega | simp_all
  · unfold adaptPred; simp
  · unfold adaptPred; simp only [show ¬ n < 0 by omega, Int.le_refl, ↓reduceIte]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sort.Assumptions]

/-- The predicate function must implement a pure boolean function over
in-bounds indices, with an arbitrary invariant `I` that it requires and
preserves. -/
def predImplements (f_code : GoFunc) (f : Int → Bool) (n : Int) (I : IProp GF) : IProp GF :=
  iprop(∀ (i : w64),
    {{ I ∗ ⌜0 ≤ sint.Z i ∧ sint.Z i < n⌝ }}
      (App (Val #f_code) (Val #i))
    {{ (r : Bool), RET #r; I ∗ ⌜r = f (sint.Z i)⌝ }})

instance predImplements_persistent (f_code : GoFunc) (f : Int → Bool) (n : Int)
    (I : IProp GF) : Persistent (predImplements f_code f n I) := by
  unfold predImplements; infer_instance

theorem predImplements_adapt (f_code : GoFunc) (f : Int → Bool) (n : Int) (I : IProp GF) :
    predImplements f_code f n I ⊢ predImplements f_code (adaptPred f n) n I := by
  unfold predImplements
  iintro #H %i
  wp_start_folded as ⟨HI, %Hb⟩
  iapply H $$ [HI]
  · iframe HI; ipureintro; exact Hb
  inext
  iintro %r ⟨HI, %Hr⟩
  iapply HΦ
  iframe HI
  ipureintro
  rw [adaptPred_bounded _ _ _ Hb]
  exact Hr

theorem wp_Search (n : w64) (f_code : GoFunc) (f : Int → Bool) (I : IProp GF) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗
        ⌜0 ≤ sint.Z n⌝ ∗
        predImplements f_code f (sint.Z n) I ∗
        I ∗
        ⌜IsMonoPred f (sint.Z n)⌝ }}
      (App (App (Val (@! Search)) (Val #n)) (Val #f_code))
    {{ (i : w64), RET #i;
        I ∗
        ⌜0 ≤ sint.Z i⌝ ∗
        ⌜sint.Z i < sint.Z n → f (sint.Z i) = true⌝ ∗
        ⌜(∀ i, 0 ≤ i ∧ i < sint.Z n → f i = false) → sint.Z i = sint.Z n⌝ ∗
        ⌜∀ k, 0 ≤ k ∧ k < sint.Z i → f k = false⌝ }} := by
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

/-- TODO: should be equivalent to `Sorted`, but couldn't find a lemma relating
that to list lookup. -/
def ListSorted {A : Type} (R : A → A → Prop) (l : List A) : Prop :=
  ∀ (i j : Nat), i < j → ∀ (xi xj : A), l[i]? = some xi → l[j]? = some xj → R xi xj

def searchF (x : w64) (xs : List w64) : Int → Bool :=
  fun i => match xs[i.toNat]? with
    | some x0 => decide (sint.Z x ≤ sint.Z x0)
    | none => true -- arbitrary, unreachable

theorem searchF_true (x : w64) (xs : List w64) (i : Int) (x_i : w64)
    (h : xs[i.toNat]? = some x_i) : searchF x xs i = true ↔ sint.Z x ≤ sint.Z x_i := by
  unfold searchF; rw [h]; simp

theorem searchF_false (x : w64) (xs : List w64) (i : Int) (x_i : w64)
    (h : xs[i.toNat]? = some x_i) : searchF x xs i = false ↔ sint.Z x_i < sint.Z x := by
  unfold searchF; rw [h]; simp

theorem wp_SearchInts (a : GoSlice) (x : w64) (q : DFrac) (xs : List w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sort ∗ a ↦*{q} xs ∗
        ⌜ListSorted (fun (i j : w64) => sint.Z i ≤ sint.Z j) xs⌝ }}
      (App (App (Val (@! SearchInts)) (Val #a)) (Val #x))
    {{ (i : w64), RET #i; a ↦*{q} xs ∗
        ⌜(∀ (j : Nat) x0, (j : Int) < sint.Z i → xs[j]? = some x0 → sint.Z x0 < sint.Z x) ∧
         (∀ (j : Nat) x0, sint.Z i ≤ (j : Int) → xs[j]? = some x0 → sint.Z x ≤ sint.Z x0)⌝ }} := by
  wp_start as ⟨Ha, %Hsort⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Ha
  ipersist x
  ipersist a
  wp_pures
  rw [show ∀ x b, (RecV BAnon x b : val) = #(func.mk BAnon x b) from
    fun x b => by rw [go.intoVal_unfold GoFunc]]
  wp_apply wp_Search _ _ (searchF x xs) iprop(a ↦*{q} xs) $$ [Ha]
  · iframe Ha
    isplitl []
    · ipureintro; omega
    isplitl []
    · unfold predImplements
      iintro %i
      wp_start as ⟨Ha, %Hbound⟩
      wp_auto
      list_elem xs (sint.nat i) as x_i
      simp only [Hbound.1, Hbound.2, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index a (sint.Z i) xs q x_i Hbound.1 $$ [Ha] with Ha
      · iframe Ha; ipureintro; exact Hx_i_lookup
      iapply HΦ
      iframe Ha
      ipureintro
      unfold searchF
      rw [show (sint.Z i).toNat = sint.nat i from rfl, Hx_i_lookup]
    · ipureintro
      intro i j Hij Hfi
      list_elem xs i.toNat as x_i
      list_elem xs j.toNat as x_j
      rw [searchF_true _ _ _ _ Hx_i_lookup] at Hfi
      rw [searchF_true _ _ _ _ Hx_j_lookup]
      have := Hsort i.toNat j.toNat (by omega) _ _ Hx_i_lookup Hx_j_lookup
      omega
  iintro %i ⟨Ha, %Hi_nn, %Hfound, %Hoob, %Hgt⟩
  wp_auto
  iapply HΦ
  iframe Ha
  ipureintro
  by_cases hin : sint.Z i < sint.Z a.len
  · -- returned index is in-bounds
    have Hfound := Hfound hin
    list_elem xs (sint.nat i) as xi
    rw [searchF_true _ _ _ _ Hxi_lookup] at Hfound
    constructor
    · intro j xj Hj_bound Hget_j
      have Hget_j' := Hgt (j : Int) (by omega)
      rw [searchF_false _ _ _ _ (by simpa using Hget_j)] at Hget_j'
      exact Hget_j'
    · intro j xj Hj_bound Hget_j
      by_cases hij : sint.nat i = j
      · subst hij
        rw [Hxi_lookup] at Hget_j
        cases Hget_j
        exact Hfound
      · have := Hsort (sint.nat i) j (by word) _ _ Hxi_lookup Hget_j
        simp only at this
        omega
  · -- `i` is out-of-bounds (larger than the list length)
    constructor
    · intro j xj Hj_bound Hget_j
      have Hget_j' := Hgt (j : Int) (by omega)
      rw [searchF_false _ _ _ _ (by simpa using Hget_j)] at Hget_j'
      exact Hget_j'
    · intro j xj Hj_bound Hget_j
      have := lookup_lt_Some Hget_j
      have := Hlen.1
      word

end proof

end sort

end Perennial
end
