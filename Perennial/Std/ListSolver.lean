/-
Port of `src/Helpers/ListSolver.v`, plus stdpp's `list_simplifier`.

Tactics:
* `list_simplifier`: simplify list expressions everywhere with the
  `@[list_simp]` and `@[len]` simp sets: lookups in `++`/`take`/`drop`/`set`/
  `replicate`/`map`, lengths, and `take`/`drop` of appends; index side
  conditions (`i < l.length`, ...) are discharged by `omega` after length
  simplification.
* `list_solver`: best-effort solver for list goals: equalities (pointwise, by
  `List.ext_getElem?`), prefixes (via `list_prefix_bounded`), lookups and
  lengths. It turns hypotheses `l₁ = l₂` and `l₁ <+: l₂` into length and
  lookup facts, simplifies, case-splits and finishes with `omega`/`simp_all`.
-/
import Perennial.Std.ListLen

namespace Perennial

section list
variable {A : Type u}

theorem list_prefix_refl (l : List A) : l <+: l := List.prefix_refl l

theorem list_lookup_eq (l : List A) (i₁ i₂ : Nat) (h : i₁ = i₂) : l !! i₁ = l !! i₂ := by rw [h]

theorem list_eq_length {l₁ l₂ : List A} (h : l₁ = l₂) : l₁.length = l₂.length := by rw [h]

theorem list_eq_forall {l₁ l₂ : List A} (h : l₁ = l₂) : ∀ i, l₁ !! i = l₂ !! i := by
  intro i; rw [h]

theorem list_prefix_forall {l₁ l₂ : List A} (h : l₁ <+: l₂) :
    ∀ i, i < l₁.length → l₁ !! i = l₂ !! i := fun _ hi => prefix_lookup_lt hi h

theorem list_eq_bounded (l₁ l₂ : List A) (hlen : l₁.length = l₂.length)
    (h : ∀ i, i < l₁.length → l₁ !! i = l₂ !! i) : l₁ = l₂ := by
  apply List.ext_getElem?; intro i
  by_cases hi : i < l₁.length
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

theorem list_prefix_bounded (l₁ l₂ : List A) (hlen : l₁.length ≤ l₂.length)
    (h : ∀ i, i < l₁.length → l₁ !! i = l₂ !! i) : l₁ <+: l₂ := by
  refine ⟨l₂.drop l₁.length, ?_⟩
  apply list_eq_bounded
  · simp; omega
  · intro i hi
    simp only [List.length_append, List.length_drop] at hi
    by_cases hi' : i < l₁.length
    · rw [List.getElem?_append_left hi', h i hi']
    · rw [List.getElem?_append_right (by omega), List.getElem?_drop]; congr 1; omega

end list

attribute [list_simp] List.getElem?_append_left List.getElem?_append_right
  List.getElem?_take_of_lt List.getElem?_take_eq_none List.getElem?_drop
  List.getElem?_set_ne List.getElem?_set_self List.getElem?_map List.getElem?_replicate
  List.getElem?_nil List.getElem?_cons_zero List.getElem?_cons_succ
  List.take_of_length_le List.drop_of_length_le List.take_append_of_le_length
  List.drop_append_of_le_length List.take_take List.drop_drop List.take_zero List.drop_zero
  List.take_nil List.drop_nil List.append_assoc List.cons_append List.nil_append List.append_nil
  List.take_left List.drop_left List.map_append List.map_take List.map_drop
  List.set_eq_of_length_le List.length_eq_zero_iff Nat.sub_self Nat.add_sub_cancel
  Nat.add_sub_cancel_left Nat.sub_zero Nat.zero_add Nat.add_zero

/-- Discharger for `list_simplifier`: arithmetic on (simplified) lengths. -/
macro "list_disch" : tactic => `(tactic| first | omega | (word_filter iris; simp only [len] at *; omega))

/-- stdpp `list_simplifier` (see the module docstring). -/
macro "list_simplifier" : tactic => `(tactic|
  simp_pure simp (disch := list_disch) only [list_simp, len])

open Lean Elab Tactic Term Meta in
/-- Rocq `find_list_hyps`: for each hypothesis `l₁ = l₂` (lists) or `l₁ <+: l₂`,
add its length and pointwise-lookup consequences. -/
elab "find_list_hyps" : tactic => withMainContext do
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← whnfR (← instantiateMVars h.type)
    let hs ← exprToSyntax h.toExpr
    if ty.isAppOfArity ``Eq 3 && (ty.getArg! 0).isAppOf ``List then
      evalTactic (← `(tactic| have := list_eq_length $hs; have := list_eq_forall $hs))
    else if ty.isAppOfArity ``List.IsPrefix 3 then
      evalTactic (← `(tactic| have := prefix_length $hs; have := list_prefix_forall $hs))

/-- Best-effort list solver (see the module docstring). -/
macro "list_solver" : tactic => `(tactic| (
  intros
  find_list_hyps
  first
  | (apply list_prefix_bounded
     · (try list_simplifier) <;> first | omega | (simp_all; done) | grind
     · intro i hi
       (try list_simplifier)
       repeat' split
       all_goals first | rfl | omega | (simp_all; done) | grind)
  | (apply List.ext_getElem?; intro i
     (try list_simplifier)
     repeat' split
     all_goals first | rfl | omega | (simp_all; done) | grind)
  | ((try list_simplifier) <;> first | done | rfl | omega | (simp_all; done) | grind)))

section tests
variable {A : Type u}

example (l : List A) (n : Nat) (h : n ≤ l.length) : l.take n ++ l.drop n = l := by list_solver

example (l : List A) : [] <+: l := by list_solver

example (l₁ l₂ : List A) (h : l₂.length ≤ l₁.length) (hp : l₁ <+: l₂) : l₁ = l₂ := by list_solver

example (l₁ l₂ : List A) (x : A) (i : Nat) (h : i < l₁.length) :
    (l₁ ++ x :: l₂) !! i = l₁ !! i := by list_simplifier

example (l₁ l₂ : List A) (x : A) : (l₁ ++ x :: l₂) !! l₁.length = some x := by list_simplifier

example (l : List A) (x : A) (i j : Nat) (h : i ≠ j) : (<[i := x]> l) !! j = l !! j := by
  list_simplifier

example (l : List A) (n : Nat) (i : Nat) (h : i + n < l.length) : (l.drop n) !! i = l !! (n + i) := by
  list_simplifier

end tests

end Perennial
