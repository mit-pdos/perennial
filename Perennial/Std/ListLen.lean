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

/-- Rocq `len`: simplify list lengths, then try `word`. -/
macro "len" : tactic => `(tactic| ((try simp only [len, uint.nat, uint.Z] at *) <;> try word))

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
