/-
Axiom/sorry audit of the Lean development.  Not part of the lakefile; run with

    lake env lean --run etc/lean-audit.lean [MODULE... | @FILE]  > audit.json

(normally via `etc/lean-audit.py`, which picks the modules that built, runs
this and writes the report).

With no arguments every `Perennial/**/*.lean` that has an `.olean` is imported.
Module names are dotted and unquoted (`Perennial.Proof.unsafe`); `@FILE` reads
one per line.

For every constant declared in a `Perennial*` module it computes the set of
axioms it transitively depends on (the same closure as `#print axioms` /
`Lean.collectAxioms`, memoized over the whole environment) and prints one JSON
object per line:

  {"t":"decl", ...}   a Perennial constant whose axioms are not all in
                      {propext, Classical.choice, Quot.sound}; fields:
                      name, root (user-facing declaration the constant belongs
                      to: aux `_proof_n`/`match_n`/private names are mapped to
                      their parent), module, kind, axioms, direct (sorryAx
                      occurs in its own type/value), synthetic (a `sorryAx _ true`,
                      i.e. an elaboration error, occurs), line, endLine.
                      partial (an `opaque` made by `partial def`).
                      Also emitted for every `axiom` and `opaque` constant.
  {"t":"axiom", ...}  every axiom reachable from a Perennial constant
                      (name, module, line)
  {"t":"extsorry",...} a non-Perennial constant (iris-lean, ...) reachable from
                      Perennial that uses `sorryAx` directly
  {"t":"module", ...} per-module totals: decls, clean, sorry, otherAx
-/
import Lean
open Lean

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def jstr (s : String) : String := (Json.str s).compress

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => .anonymous

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

/-- Does `sorryAx _ true` (a synthetic sorry from an elaboration error) occur? -/
def hasSyntheticSorry (e : Expr) : Bool :=
  (e.find? fun e => e.isAppOfArity ``sorryAx 2 && e.appArg! == mkConst ``Bool.true).isSome

def ciExprs (ci : ConstantInfo) : List Expr :=
  ci.type :: (match ci.value? (allowOpaque := true) with | some v => [v] | none => [])

/-- Memoized transitive axiom closure (iterative DFS; constants on a cycle see
the partial result, as in `collectAxioms`). -/
partial def axiomClosure (env : Environment) (roots : Array Name) :
    IO (Std.HashMap Name (Array Name)) := do
  let mut memo : Std.HashMap Name (Array Name) := {}
  let mut onStack : NameSet := {}
  for r in roots do
    if memo.contains r then continue
    -- stack of (name, children-pushed?)
    let mut stack : Array (Name × Bool) := #[(r, false)]
    while h : stack.size > 0 do
      let (n, expanded) := stack.back
      if memo.contains n then
        stack := stack.pop; continue
      match env.find? n with
      | none => memo := memo.insert n #[]; stack := stack.pop
      | some ci =>
        let deps := ci.getUsedConstantsAsSet
        if !expanded then
          stack := stack.set! (stack.size - 1) (n, true)
          onStack := onStack.insert n
          for d in deps do
            if !memo.contains d && !onStack.contains d then
              stack := stack.push (d, false)
        else
          let mut acc : Array Name := if ci matches .axiomInfo _ then #[n] else #[]
          for d in deps do
            for a in memo.getD d #[] do
              if !acc.contains a then acc := acc.push a
          memo := memo.insert n acc
          onStack := onStack.erase n
          stack := stack.pop
  return memo

/-- The user-facing declaration a constant belongs to, and its source range. -/
partial def rootOf (env : Environment) (n : Name) : Name × Option DeclarationRanges :=
  let rec go (m : Name) : Option (Name × DeclarationRanges) :=
    match m with
    | .anonymous => none
    | _ =>
      if isPrivatePrefix m && !isPrivateName m then none else
      let here := if (env.find? m).isSome then (declRangeExt.find? env m (level := .private)) else none
      match here with
      | some r => some (m, r)
      | none => go m.getPrefix
  -- the nearest enclosing constant (itself first) that has a source range:
  -- aux constants (`_proof_n`, `match_n`, `eq_n`, ...) have none
  match go n with
  | some (m, r) => (privateToUserName m, some r)
  | none => (privateToUserName n, none)

def readModules (args : List String) : IO (Array Name) := do
  let mut out := #[]
  for a in args do
    if a.startsWith "@" then
      for l in (← IO.FS.lines (a.drop 1).toString) do
        let l := l.trimAscii.toString
        if !l.isEmpty then out := out.push l.toName
    else out := out.push a.toName
  if !out.isEmpty then return out
  -- default: every Perennial source with an olean
  let files ← System.FilePath.walkDir "Perennial"
  let mut ms := #[`Perennial]
  for f in files do
    if f.extension == some "lean" then
      let rel := (f.withExtension "").toString
      let olean : System.FilePath := ".lake/build/lib/lean" / (rel ++ ".olean")
      if ← olean.pathExists then
        ms := ms.push (rel.replace "/" ".").toName
  return ms

/-- `String.toName` splits on `.` and needs no «» quoting, but strip it anyway. -/
def cleanName (n : Name) : Name :=
  (n.toString (escape := false)).replace "«" "" |>.replace "»" "" |>.toName

def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mods := (← readModules args).map cleanName
  let mods := mods.filter (!·.isAnonymous)
  IO.eprintln s!"lean-audit: importing {mods.size} modules"
  let env ← importModules (mods.map fun m => { module := m }) {}
  let isPerennial (m : Name) : Bool := m.getRoot == `Perennial
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.map₁.toList do
    if isPerennial (modOf env n) then roots := roots.push n
  IO.eprintln s!"lean-audit: {roots.size} Perennial constants; computing axiom closure"
  let memo ← axiomClosure env roots
  let mut axiomsSeen : NameSet := {}
  -- per-module counts: decls, clean, sorry, otherAx
  let mut perMod : Std.HashMap Name (Nat × Nat × Nat × Nat) := {}
  let out ← IO.getStdout
  for n in roots do
    let some ci := env.find? n | continue
    let m := modOf env n
    let axs := memo.getD n #[]
    for a in axs do axiomsSeen := axiomsSeen.insert a
    let nonstd := axs.filter (!standardAxioms.contains ·)
    let hasSorry := nonstd.contains ``sorryAx
    let hasOther := nonstd.any (· != ``sorryAx)
    let (d, c, s, o) := perMod.getD m (0, 0, 0, 0)
    perMod := perMod.insert m (d + 1, c + (if nonstd.isEmpty then 1 else 0),
      s + (if hasSorry then 1 else 0), o + (if hasOther then 1 else 0))
    if nonstd.isEmpty && !(ci matches .axiomInfo _) && !(ci matches .opaqueInfo _) then continue
    let direct := ci.getUsedConstantsAsSet.contains ``sorryAx
    let synthetic := direct && (ciExprs ci).any hasSyntheticSorry
    let (root, rng) := rootOf env n
    let (line, endLine) := match rng with
      | some r => (r.range.pos.line, r.range.endPos.line) | none => (0, 0)
    let axJson := ",".intercalate (nonstd.toList.map (jstr ·.toString))
    out.putStrLn s!"\{\"t\":\"decl\",\"name\":{jstr n.toString},\"root\":{jstr root.toString},\"module\":{jstr m.toString},\"kind\":{jstr (kindOf ci)},\"axioms\":[{axJson}],\"direct\":{direct},\"synthetic\":{synthetic},\"partial\":{env.contains (n.str "_unsafe_rec")},\"line\":{line},\"endLine\":{endLine}}"
  for a in axiomsSeen.toList do
    let line := match declRangeExt.find? env a (level := .private) with
      | some r => r.range.pos.line | none => 0
    out.putStrLn s!"\{\"t\":\"axiom\",\"name\":{jstr a.toString},\"module\":{jstr (modOf env a).toString},\"line\":{line}}"
  -- sorries outside Perennial (iris-lean, batteries, ...) that Perennial reaches
  for (n, axs) in memo.toList do
    if !axs.contains ``sorryAx || isPerennial (modOf env n) then continue
    let some ci := env.find? n | continue
    if ci.getUsedConstantsAsSet.contains ``sorryAx then
      out.putStrLn s!"\{\"t\":\"extsorry\",\"name\":{jstr n.toString},\"module\":{jstr (modOf env n).toString}}"
  for (m, (d, c, s, o)) in perMod.toList do
    out.putStrLn s!"\{\"t\":\"module\",\"module\":{jstr m.toString},\"decls\":{d},\"clean\":{c},\"sorry\":{s},\"otherAx\":{o}}"
  return 0
