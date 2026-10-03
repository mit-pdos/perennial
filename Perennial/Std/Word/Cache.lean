/-
A cache of `word` proofs, so that a `word` goal that is elaborated again in the
same context (the same side condition elaborated twice by `wp_apply`'s
unification retries, the same goal after `and_intros`/`<;>` duplication, ...) is
not proved again. Used by `word` (`Perennial/Std/Word/Automation.lean`).

A cached proof is reused only when the goal is syntactically the same and every
free variable of the proof is declared in the current context exactly as when
the proof was found (and every constant it uses exists), so the proof is valid
as is (the kernel checks it again in any case).
-/
import Lean

namespace Perennial.word
open Lean Meta

structure CacheEntry where
  goal : Expr
  proof : Expr
  /-- The declarations of the free variables of `goal` and `proof`. -/
  decls : Array LocalDecl
  consts : Array Name

initialize wordCache : IO.Ref (Std.HashMap UInt64 (Array CacheEntry)) ← IO.mkRef {}

/-- Entries beyond this many goals are dropped (the cache is cleared). -/
def cacheMax : Nat := 4096

/-- A cached proof of `goal` that is valid in the current context. -/
def cacheLookup (goal : Expr) : MetaM (Option Expr) := do
  let some es := (← wordCache.get)[goal.hash]? | return none
  let lctx ← getLCtx
  let env ← getEnv
  for e in es do
    unless e.goal == goal do continue
    let ok := e.decls.all fun d =>
      match lctx.find? d.fvarId with
      | some d' => d'.type == d.type && d'.value? == d.value? && d'.isLet == d.isLet
      | none => false
    if ok && e.consts.all env.contains then return some e.proof
  return none

/-- Record the proof `proof` of `goal` (no metavariables, no `sorry`). -/
def cacheStore (goal proof : Expr) : MetaM Unit := do
  if proof.hasMVar || proof.hasSorry || goal.hasMVar then return
  let lctx ← getLCtx
  let fvs := (collectFVars (collectFVars {} goal) proof).fvarIds
  let mut decls := #[]
  for x in fvs do
    let some d := lctx.find? x | return
    decls := decls.push d
  let entry : CacheEntry := { goal, proof, decls, consts := proof.getUsedConstants }
  wordCache.modify fun m =>
    let m := if m.size ≥ cacheMax then {} else m
    m.insert goal.hash ((m.getD goal.hash #[]).push entry)

/-- Goals that `omega` failed to prove, with the hypotheses it had (`omega` is
deterministic, so it fails again on the same goal with the same hypotheses). -/
initialize failCache : IO.Ref (Std.HashMap UInt64 (Array (Expr × Array (FVarId × Expr)))) ←
  IO.mkRef {}

/-- The propositions of the current context (what `omega` can use). -/
def propContext : MetaM (Array (FVarId × Expr)) := do
  let mut r := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ← isProp ty then r := r.push (d.fvarId, ty)
  return r

def failLookup (goal : Expr) (ctx : Array (FVarId × Expr)) : IO Bool := do
  let some es := (← failCache.get)[goal.hash]? | return false
  return es.any fun (g, c) => g == goal && c == ctx

def failStore (goal : Expr) (ctx : Array (FVarId × Expr)) : IO Unit :=
  failCache.modify fun m =>
    let m := if m.size ≥ cacheMax then {} else m
    m.insert goal.hash ((m.getD goal.hash #[]).push (goal, ctx))

end Perennial.word
