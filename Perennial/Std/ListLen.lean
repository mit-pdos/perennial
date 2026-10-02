/-
Port of `src/Helpers/ListLen.v`: the `len` tactic.

Rocq's `len` rewrites with the `len` hint database and then tries `word` and
`lia`. Here `len` simplifies with the `@[len]` simp set (everywhere) and then
tries `word` (which subsumes `omega`). Like Rocq, it does not fail if the goal
remains. Add your own rules with `attribute [len] foo_length`.
-/
import Perennial.Std.ListBasics
import Perennial.Std.Word.Automation

namespace Perennial

open Lean Elab Tactic Meta in
/-- `simp_pure (simp ...)`: run the given `simp` call (without location) at the
hypotheses and the goal that do not mention Iris entailments, so that it stays
cheap inside large Iris proof mode goals. Fails if nothing changes (like
`simp at *`). -/
elab "simp_pure " s:tactic : tactic => withMainContext do
  let mut fvars := #[]
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    unless ← isProp ty do continue
    if word.mentionsEntailment ty then continue
    fvars := fvars.push h.fvarId
  let tgt ← instantiateMVars (← getMainTarget)
  let simpTgt := !word.mentionsEntailment tgt
  let { ctx, simprocs, dischargeWrapper, .. } ← mkSimpContext s (eraseLocal := false)
  let g ← getMainGoal
  let (result?, _) ← dischargeWrapper.with fun discharge? =>
    simpGoal g ctx (simprocs := simprocs) (discharge? := discharge?)
      (simplifyTarget := simpTgt) (fvarIdsToSimp := fvars)
  match result? with
  | none => replaceMainGoal []
  | some (_, m) =>
    if m == g then throwError "simp_pure: simp made no progress"
    replaceMainGoal [m]

/-- Internal: `simp only [len, uint.nat, uint.Z]` at the hypotheses and the goal that
do not mention Iris entailments. Does not fail. -/
macro "len_simp" : tactic => `(tactic| try simp_pure simp only [len, uint.nat, uint.Z])

open Lean Elab Tactic Meta in
/-- Internal: is the main goal free of Iris entailments? -/
elab "guard_pure_target" : tactic => withMainContext do
  if word.mentionsEntailment (← instantiateMVars (← getMainTarget)) then
    throwError "the goal is an Iris goal"

/-- Rocq `len`: simplify list lengths (`@[len]` simp set) in the goal and the
hypotheses, then try `word`. Hypotheses and goals that mention Iris entailments
(e.g. the Iris proof mode goal) are not touched, so `len` is cheap inside large
Iris proofs; on an Iris goal, `word` is only used to find a contradiction in the
pure hypotheses. -/
macro "len" : tactic => `(tactic| (len_simp; first
  | (guard_pure_target; try word)
  | (try (exfalso; word))))

/-- Rocq `list_elem l i as x`: obtain `x` and `Hx_lookup : l !! i = some x`,
proving the bound `i < l.length` with `len`. The index must be a `Nat`
(write `list_elem l (uint.nat i) as x` for a word index). -/
syntax "list_elem " term:max ppSpace term:max " as " ident : tactic
macro_rules
  | `(tactic| list_elem $l $i as $x) =>
    let h := Lean.mkIdent (Lean.Name.mkSimple ("H" ++ x.getId.toString ++ "_lookup"))
    `(tactic| obtain ⟨$x, $h⟩ := lookup_lt_is_Some_2 (l := $l) (i := $i) (by len))

section tests
example (l1 l2 : List Nat) (x : Nat) : (l1 ++ x :: l2).length = l1.length + l2.length + 1 := by len
example (l : List Nat) (n : Nat) (h : n ≤ l.length) : (l.take n ++ [3]).length = n + 1 := by len
example (l : List Nat) (h : 2 < l.length) : True := by
  list_elem l 2 as y
  trivial
end tests

end Perennial
