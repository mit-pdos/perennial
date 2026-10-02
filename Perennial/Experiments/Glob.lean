/-
Port of `new/experiments/glob.v`: glob patterns over Iris hypothesis names.

`iCombineNamed "pat" as Hout` combines all *spatial* hypotheses whose names
match the glob `pat` into a single hypothesis `Hout`, a separating conjunction
of named conjuncts (`"H1" ∷ P1 ∗ "H2" ∷ P2 ∗ ...`), so that `iNamed Hout`
restores them. A glob is a space-separated list of words; a word may contain one
`*`, which matches any (possibly empty) sequence of characters
(e.g. `"H*"`, `"*_wg"`, `"Hx Hy*"`).

The `iNamed`/`iNamedPrefix`/`iNamedSuffix` tactics also defined in the Rocq file
live in `Perennial/Helpers/NamedProps.lean`.
-/
import Perennial.Helpers.NamedProps

namespace Perennial

open Iris Iris.BI

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Does `s` match the glob word `w` (at most one `*`)? -/
def globWordMatches (w s : String) : Bool :=
  match w.splitOn "*" with
  | [w] => w == s
  | [pre, suf] => s.length ≥ pre.length + suf.length && s.startsWith pre && s.endsWith suf
  | _ => false

/-- Names of the spatial hypotheses (in context order). -/
def spatialHypNames {u} {prop : Q(Type u)} {bi : Q(BI $prop)} :
    ∀ {e}, Hyps bi e → List Name
  | _, .emp _ => []
  | _, .hyp _ name _ p _ _ => if isTrue p then [] else [name]
  | _, .sep _ _ _ _ lhs rhs => spatialHypNames lhs ++ spatialHypNames rhs

/-- Expand the glob `pat` against the spatial hypotheses of the main goal
(Rocq `glob_ipm`). -/
def globIpm (pat : String) : TacticM (List Name) := do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType))
    | throwError "glob: not in the Iris proof mode"
  let names := spatialHypNames g.hyps
  let words := (pat.splitOn " ").filter (· ≠ "")
  return names.filter fun n =>
    !n.hasMacroScopes && words.any (globWordMatches · n.toString)

/-- Rocq `iCombineNamed "pat" as "Hout"` (see the module docstring). -/
elab "iCombineNamed " pat:str " as " out:ident : tactic => do
  let hs ← globIpm pat.getString
  let src := s!"ihave {out.getId} : _ $$ [{" ".intercalate (hs.map toString)}]"
  let tac ← match Parser.runParserCategory (← getEnv) `tactic src with
    | .ok stx => pure stx
    | .error err => throwError "iCombineNamed: {err}"
  evalTactic tac
  -- the first goal is the assertion, from the selected hypotheses
  evalTactic (← `(tactic| iNamedAccu))

end tactics

end Perennial
