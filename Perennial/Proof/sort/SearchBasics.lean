/-
Shared definitions of the proofs of `sort.Search` and `sort.SearchInts`
(`Perennial/Spec/sort/Search.lean`, `Perennial/Spec/sort/SearchInts.lean`): predicates, their
adaptation, `predImplements`, and the predicate `SearchInts` searches with.

The specification for `sort.Search` is simpler than `sort.Find`: it takes a
predicate function (`f : Int → Bool`) and a number `n`, and it searches for the
first `i ∈ [0, n)` such that `f i = true`, assuming `f` goes from false to true.
As for `Find`, `0 ≤ n` is a precondition, `f` is only called on `[0, n)`, and
the user-provided `f` is "adapted" (`adaptPred`) so that `f (-1) = false` and
`f n = true`.
-/
module

public import Perennial.Proof.sort.FindBasics
public import Perennial.Golang.Theory.String

@[expose] public section

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

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
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

/-- The predicate `SearchStrings` searches with: whether the `i`th string is at least `x`. -/
def searchStringsF (x : GoString) (xs : List GoString) : Int → Bool :=
  fun i => match xs[i.toNat]? with
    | some x0 => decide (go.GoStringLe x x0)
    | none => true -- arbitrary, unreachable

theorem searchStringsF_true (x : GoString) (xs : List GoString) (i : Int) (x_i : GoString)
    (h : xs[i.toNat]? = some x_i) : searchStringsF x xs i = true ↔ go.GoStringLe x x_i := by
  unfold searchStringsF; rw [h]; simp

theorem searchStringsF_false (x : GoString) (xs : List GoString) (i : Int) (x_i : GoString)
    (h : xs[i.toNat]? = some x_i) : searchStringsF x xs i = false ↔ go.GoStringLt x_i x := by
  unfold searchStringsF; rw [h]
  simp only [decide_eq_false_iff_not]
  unfold go.GoStringLe
  constructor
  · intro hn
    apply Classical.byContradiction
    intro hlt
    apply hn
    by_cases h2 : go.GoStringLt x x_i
    · exact Or.inr h2
    · exact Or.inl (go.goStringLt_eq_of_not_lt h2 hlt)
  · intro hlt hle
    rcases hle with heq | hlt'
    · subst heq; exact go.goStringLt_irrefl _ hlt
    · exact go.goStringLt_asymm hlt hlt'

/-- `GoStringLe` is transitive. -/
theorem goStringLe_trans {a b c : GoString} (h1 : go.GoStringLe a b) (h2 : go.GoStringLe b c) :
    go.GoStringLe a c := by
  rcases h1 with rfl | h1
  · exact h2
  · rcases h2 with rfl | h2
    · exact Or.inr h1
    · exact Or.inr (go.goStringLt_trans h1 h2)

end defs

end sort

end Perennial
end
