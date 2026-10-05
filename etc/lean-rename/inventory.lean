import Lean
open Lean Meta

def kindOf (env : Environment) (ci : ConstantInfo) : String :=
  match ci with
  | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => if isClass env ci.name then "class" else if isStructure env ci.name then "structure" else "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"
  | .defnInfo _ => if isInstanceCore env ci.name then "instance" else if (env.getProjectionFnInfo? ci.name).isSome then "proj" else "def"

partial def resultSort (e : Expr) : MetaM String := do
  forallTelescopeReducing e fun _ b => do
    let b ← whnfR b
    match b with
    | .sort u => return if u.isZero then "Prop" else "Type"
    | _ =>
      let t ← inferType b
      match ← whnfR t with
      | .sort u => return if u.isZero then "proof" else "term"
      | _ => return "term"

def main (args : List String) : IO Unit := do
  let mods := args.map (fun s => s.toName) |>.toArray
  initSearchPath (← findSysroot)
  unsafe enableInitializersExecution
  let env ← importModules (mods.map ({module := ·})) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Core.Context := { fileName := "", fileMap := default, maxHeartbeats := 0 }
  let mut out := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    unless (`Perennial).isPrefixOf m do continue
    if n.isInternalDetail then continue
    let k := kindOf env ci
    let r ← (Prod.fst <$> ((resultSort ci.type).run' {} |>.toIO ctx {env})) <|> pure "?"
    out := out.push s!"{m}\t{n}\t{k}\t{r}"
  IO.println (String.intercalate "\n" out.toList)
