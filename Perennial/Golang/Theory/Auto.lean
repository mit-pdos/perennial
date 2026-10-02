/-
Port of `new/golang/theory/auto.v`: the user-facing automation.

* `wp_start` / `wp_start as pat` / `wp_start_folded as pat`: begin the proof of
  a Texan triple for a function or method.
* `wp_func_call`, `wp_method_call`: unfold `#(functions f ts)` /
  `#(methods t m v)` with the `FuncUnfold`/`MethodUnfold` instances.
* `wp_auto`, `wp_auto_lc n`: repeatedly take pure steps, loads, stores and
  allocations of local variables, then drop points-to facts of dead locals.
* `wp_apply lem $$ spats as pats`: apply a spec (see `wp_apply_core`), solve
  `is_pkg_init` premises, introduce `pats` in the continuation and run
  `wp_auto` (disable with `--no-auto`; `--lc n` asks for `n` later credits).
* `wp_if_destruct`, `wp_for`, `wp_for hyp`, `wp_for_post`, `wp_end`.

Differences from Rocq:
* `wp_apply ... as "%x Hx"` is written `wp_apply ... as %x Hx` (iris-lean intro
  patterns; `with` is accepted as a synonym of `as`). Lean-level binders are
  introduced with `%x` (Rocq `as (x) "..."`). The spec patterns of `wp_apply` are
  iris-lean's minus `[H] as name`, so `wp_apply lem $$ [H] as pats` works.
* Rocq's global `wp_apply_auto_default` switch is not ported; use `--no-auto`.
* `wp_if_destruct` names the case hypothesis `Hif` (Rocq leaves it anonymous)
  and substitutes it when it is an equation with a variable side. It splits on
  the condition of the `if:` at the head of the expression.
* All WP tactics fail (instead of leaving a `sorry`) when a term does not
  elaborate (`withNoSorry`).
* With `set_option goose.wp.extras true` (off by default, for backwards
  compatibility with proofs that do these steps by hand): `wp_auto` rewrites
  stored function literals to `#(func.mk ..)` and unfolds package constants
  (`def a : val := #..`) that block a step; `wp_pures`/`wp_auto` stop at slice
  composite literals (use `wp_slice_literal`, as in Rocq), reduce `match`es on
  definitions of constructors, and use the `goose_wp_simp_extra` simp set
  (`Perennial/Golang/Theory/TacticsSimp.lean`).
* `wp_func_call` only rewrites the WP expression (not the hypotheses), and (with
  `goose.wp.extras`) finds `FuncUnfold f (List.replicate n t)` instances for type
  arguments `[t, .., t]`.
* `wp_alloc_auto` (not `wp_auto`) also does anonymous allocations.
-/
import Perennial.Golang.Theory.Pkg
import Perennial.Golang.Theory.TacticsSimp

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## Function and method calls -/

section func_call
open Lean Elab Tactic Meta Qq Iris.ProofMode

theorem tac_wp_func_unfold {PROP : Type _} [BI PROP] {Δ P Q : PROP} (h : Δ ⊢ Q) (heq : P = Q) :
    Δ ⊢ P := heq ▸ h

/-- `[t, t, ..., t]` (`n` copies), as `(n, t)`. -/
partial def replicateLit? (ts : Expr) (t? : Option Expr := none) (n : Nat := 0) :
    MetaM (Option (Nat × Expr)) := do
  let ts ← whnfR ts
  if ts.isAppOfArity ``List.nil 1 then return t?.map (n, ·)
  if ts.isAppOfArity ``List.cons 3 then
    let t := ts.getArg! 1
    if let some t0 := t? then
      unless ← isDefEq t t0 do return none
    return ← replicateLit? (ts.getArg! 2) (some (t?.getD t)) (n + 1)
  return none

/-- A proof of `#(functions f ts) = impl` from a `FuncUnfold f ts impl` instance;
if none is found and `ts = [t, ..., t]`, from `FuncUnfold f (List.replicate n t) impl`
(e.g. `go.min`, `go.max`). -/
def funcUnfoldEq (fv : Expr) (f ts : Expr) : MetaM (Option Expr) := do
  let valTy ← inferType fv
  let tryInst (ts' : Expr) : MetaM (Option Expr) := do
    let impl ← mkFreshExprMVar valTy
    let ty ← mkAppM ``FuncUnfold #[f, ts', impl]
    let some inst ← synthInstance? ty | return none
    let pf ← mkAppOptM ``FuncUnfold.func_unfold #[none, none, none, none, none, none, some inst]
    let pfTy ← instantiateMVars (← inferType pf)
    let some (_, _, rhs) := pfTy.eq? | return none
    -- `#(functions f ts') = impl`, cast to `fv = impl` (definitional)
    return some (← mkExpectedTypeHint pf (← mkEq fv rhs))
  if let some p ← tryInst ts then return some p
  -- (only with `goose.wp.extras`, for backwards compatibility)
  unless goose.wp.extras.get (← getOptions) do return none
  if let some (n, t) ← replicateLit? ts then
    let rep ← mkAppM ``List.replicate #[mkNatLit n, t]
    if let some p ← tryInst rep then return some p
  return none

/-- The function value `#(functions f ts)` of the next call in the WP expression:
the innermost call `App (Val #(functions f ts)) _` in evaluation position, or else
the first `#(functions f ts)` in the expression. Returns `(#(functions f ts), f, ts)`. -/
def findFuncCall (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let isFn (fv : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
    let fv := (← instantiateMVars fv).consumeMData
    unless fv.isAppOfArity ``GoGlobalContext.into_val 4 do return none
    let x ← whnfR (fv.getArg! 3)
    unless x.isAppOfArity ``functions 6 || x.getAppFn.constName? == some ``functions do return none
    let args := x.getAppArgs
    if args.size < 2 then return none
    return some (fv, args[args.size - 2]!, args[args.size - 1]!)
  let mut found := none
  for (_, e') in ← allEctx e do
    let e' ← whnfR e'
    let_expr Perennial.expr.App _ fe _ := e' | continue
    let some fv ← isGooseVal? fe | continue
    if let some r ← isFn fv then found := some r
  if found.isSome then return found
  let some fv := (← instantiateMVars e).find? (fun s =>
      s.isAppOfArity ``GoGlobalContext.into_val 4 &&
        (s.getArg! 3).getAppFn.constName? == some ``functions) | return none
  isFn fv

end func_call

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- The core of `wp_func_call`; `false` if no call was found. -/
def wpFuncCallCore : TacticM Bool :=
  withNoSorry `wp_func_call <| ProofModeM.runTactic `wp_func_call fun mvar g => do
    let some wp ← parseGooseWp? g.goal | return false
    let some (fv, f, ts) ← findFuncCall wp.e | return false
    let some heq ← funcUnfoldEq fv f ts | return false
    let some (_, _, impl) := (← instantiateMVars (← inferType heq)).eq? | return false
    let e' := wp.e.replace fun s => if s == fv then some impl else none
    let wpE' := { wp with e := e' }
    let motive ← withLocalDeclD `x (← inferType fv) fun x => do
      let ex := wp.e.replace fun s => if s == fv then some x else none
      mkLambdaFVars #[x] (wp.mk' ex wp.Φ)
    let heq' ← mkCongrArg motive heq
    let pf ← addBIGoal g.hyps (wpE'.mk' e' wp.Φ)
    mvar.assign (← mkAppNamed ``tac_wp_func_unfold
      [("Δ", g.e), ("P", g.goal), ("Q", wpE'.mk' e' wp.Φ), ("!h", pf), ("!heq", heq')])
    return true

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Rocq `wp_func_call`: unfold the function value `#(functions f ts)` of the next
call in the WP expression (see `findFuncCall`) with its `FuncUnfold` instance
(with `goose.wp.extras`, also for type arguments `[t, ..., t]` matching an
instance for `List.replicate n t`), then try to solve `is_pkg_init` goals. Only the WP
expression is rewritten (all occurrences of that function value in it), not the
hypotheses. Falls back to `rw [func_unfold]`. -/
elab "wp_func_call" : tactic => do
  let saved ← saveState
  let done ← try wpFuncCallCore catch _ => pure false
  unless done do
    saved.restore
    evalTactic (← `(tactic| rw [func_unfold]))
  evalTactic (← `(tactic| try iPkgInit))

/-- Rocq `wp_method_call`: rewrite `#(methods t m v)` with its `MethodUnfold`
instance and try to solve `is_pkg_init` goals. -/
macro "wp_method_call" : tactic => `(tactic| (rw [method_unfold]; (try iPkgInit)))

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Is `e` (up to `named`) `is_pkg_init _`? -/
def isPkgInitProp (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isAppOfArity ``is_pkg_init 4

/-- Rocq `destruct_pkg_init H`: move the `is_pkg_init` conjuncts at the front of
`H` to the intuitionistic context. Returns `false` if `H` was entirely an
`is_pkg_init` (and is now gone). -/
partial def destructPkgInit (h : Name) : TacticM Bool := do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return true
  let some (_, ty) := g.hyps.find? h | return false
  let ty' ← whnfR (← instantiateMVars ty)
  if ty'.isAppOfArity ``BIBase.sep 4 then
    if ← isPkgInitProp (ty'.getArg! 2) then
      evalTactic (← `(tactic| icases $(mkIdent h):ident with ⟨#_, $(mkIdent h):ident⟩))
      return ← destructPkgInit h
    return true
  if ← isPkgInitProp ty' then
    evalTactic (← `(tactic| icases $(mkIdent h):ident with #_))
    return false
  if ty'.isAppOfArity ``BIBase.emp 2 then
    evalTactic (← `(tactic| iclear $(mkIdent h):ident))
    return false
  return true

/-- The fields `(is_pkg_init_deps, is_pkg_init_def)` of an `IsPkgInit`
instance, obtained by unfolding the instance constant (e.g. one built with
`define_is_pkg_init`) to an `IsPkgInit.mk` application. -/
partial def pkgInitInstFields (inst : Expr) (fuel : Nat := 20) : MetaM (Option (Expr × Expr)) := do
  let inst := (← instantiateMVars inst).headBeta
  if inst.isAppOfArity ``IsPkgInit.mk 5 then return some (inst.getArg! 3, inst.getArg! 4)
  if fuel == 0 then return none
  match ← unfoldDefinition? inst with
  | some i => pkgInitInstFields i (fuel - 1)
  | none => return none

/-- Rocq `iEval (rewrite is_pkg_init_unfold /=)`: in the conclusion of the
Iris goal, unfold `is_pkg_init pkg` into
`□ deps ∗ □ P`, where `deps`/`P` are the fields of the
`IsPkgInit` instance (so the dependencies appear as `is_pkg_init dep ∗ ... ∗ True`).
The change is definitional (checked by the kernel). -/
elab "is_pkg_init_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some #[prop, bi, P, Q] := t.consumeMData.appM? ``Entails'
    | throwError "is_pkg_init_unfold: not an Iris goal"
  let Q' ← Meta.transform Q (pre := fun e => do
    if e.isAppOfArity ``is_pkg_init 4 then
      let some (deps, d) ← pkgInitInstFields (e.getArg! 3) | return .continue
      let pkg := e.getArg! 2
      let body ← mkAppOptM ``is_pkg_init_wrap #[e.getArg! 0, e.getArg! 1, pkg, e.getArg! 3]
      let some body ← unfoldDefinition? body | return .continue
      let body ← Meta.transform body (pre := fun x => do
        if x.isAppOfArity ``IsPkgInit.is_pkg_init_deps 4 && x.getArg! 2 == pkg then return .done deps
        if x.isAppOfArity ``IsPkgInit.is_pkg_init_def 4 && x.getArg! 2 == pkg then return .done d
        if x.isAppOfArity ``named 3 then return .visit (x.getArg! 2)
        return .continue)
      return .done body
    return .continue)
  let t' := mkApp4 t.consumeMData.getAppFn prop bi P Q'
  replaceMainGoal [← g.replaceTargetDefEq t']

end tactics

/-- Rocq `wp_start_folded as pat`: introduce `Φ`, the precondition `Hpre` and
the continuation `HΦ` of a Texan triple; move `is_pkg_init` facts of the
precondition to the intuitionistic context; destruct the rest with `pat`.
Does not unfold the function being called. -/
syntax "wp_start_folded" (" as " icasesPat)? : tactic

open Lean Elab Tactic in
set_option hygiene false in
elab_rules : tactic
  | `(tactic| wp_start_folded $[as $pat?]?) => do
    evalTactic (← `(tactic| try imodintro))
    evalTactic (← `(tactic| iintro %Φ Hpre HΦ))
    let present ← destructPkgInit `Hpre
    if present then
      if let some pat := pat? then
        evalTactic (← `(tactic| icases Hpre with $pat))

/-- Rocq `wp_start as pat`: `wp_start_folded as pat`, then unfold the function
(`wp_func_call`) or method (`wp_method_call`) being called and take the call
steps (`wp_call`). `wp_start` keeps the precondition as `Hpre`. -/
syntax "wp_start" (" as " icasesPat)? : tactic

macro_rules
  | `(tactic| wp_start as $p:icasesPat) =>
    `(tactic| (wp_start_folded as $p; (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)))
  | `(tactic| wp_start) =>
    `(tactic| (wp_start_folded; (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)))

/-- Finish the proof of a package's `wp_initialize'` (Rocq
`iEval (rewrite is_pkg_init_unfold /=). iFrame "∗#".`): unfold `is_pkg_init`
in the goal (`is_pkg_init_unfold`) and frame the dependencies' `is_pkg_init`
facts from the intuitionistic context. -/
macro "is_pkg_init_finish" : tactic => `(tactic| (
  is_pkg_init_unfold
  (try imodintro)
  (try iframe #)
  (try (imodintro; itrivial))
  (try itrivial)))

/-! ## `wp_auto` -/

section auto
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Hypotheses `l ↦{dq} v` whose location `l` is a local variable that occurs
nowhere else (Rocq `wp_clear_unused_pointsto`). -/
def unusedPointsto {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Expr) : MetaM (List (IVarId × FVarId)) := do
  let goal ← instantiateMVars goal
  if goal.hasExprMVar then return []
  let hs := hypsList hyps
  let mut res := []
  for (_, ivar, p, ty) in hs do
    if isTrue p then continue
    let ty ← instantiateMVars ty
    unless ty.isAppOfArity ``typed_pointsto 6 do continue
    let l := ty.getArg! 3
    let .fvar lid := l | continue
    -- `l` must not occur in the goal, in other hypotheses, or in the Lean context
    if goal.containsFVar lid then continue
    let mut used := false
    for (_, ivar', _, ty') in hs do
      if ivar' != ivar && (← instantiateMVars ty').containsFVar lid then used := true
    if (ty.getArg! 4).containsFVar lid || (ty.getArg! 5).containsFVar lid then used := true
    for decl in ← getLCtx do
      if decl.fvarId != lid && !decl.isImplementationDetail then
        if (← instantiateMVars decl.type).containsFVar lid then used := true
        if let some v := decl.value? then
          if v.containsFVar lid then used := true
    if (res.map (·.2)).contains lid then used := true
    unless used do res := (ivar, lid) :: res
  return res

theorem tac_clear_hyp {PROP : Type _} [BI PROP] [BIAffine PROP] {Δ Δ' P Q : PROP}
    (h : Δ ⊣⊢ Δ' ∗ P) (h' : Δ' ⊢ Q) : Δ ⊢ Q :=
  h.1.trans (sep_elim_left.trans h')

/-- Add the final goal `hyps ⊢ goal`, after clearing the points-to facts of
dead local variables. -/
def addGoalCleaning {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Expr) : ProofModeM Expr := do
  let unused ← unusedPointsto hyps goal
  if unused.isEmpty then return ← addBIGoal hyps goal
  -- remove the hypotheses one by one, building the proof
  let rec go {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (us : List (IVarId × FVarId)) :
      ProofModeM Expr := do
    match us with
    | [] => addBIGoalWithoutFVars (u := u) hyps goal (unused.map (·.2)).toArray
    | (ivar, _) :: us =>
      let r := hyps.remove false ivar
      let pf ← go r.hyps' us
      mkAppNamed ``tac_clear_hyp [("h", r.pf), ("Q", goal), ("!h'", pf)]
  go hyps unused

/-- Rocq `wp_auto_lc`: repeatedly take pure steps (the first `lc` of them
keeping their later credit, introduced as `Hlc1`, `Hlc2`, ...), loads, stores
and `let:`-allocations; when the expression becomes a value, continue in the
postcondition if it is again a WP. At the end, points-to facts of dead locals
are cleared. Returns the proof, the number of credits still wanted and whether
progress was made.

Performance notes: the expression is kept in `goose_wp_simp` normal form, so
`simp` is only run on the whole expression when a newly inserted value (e.g. a
loaded `#v`) could be simplified (`simpOnlyIf`); substitutions get kernel-cheap
proofs (`substPf`); the later introduced by a pure step is `laterN_intro` unless
a hypothesis contains `▷` (`iLaterIntro`); loads and stores try the points-to at
the same address first (`hypsListFor`); allocations do not re-abstract the
continuation proof (`iWpAllocStep`). Together these make `wp_auto` roughly linear
in the length of straight-line code.

Only the search for the next step may fail silently; an error while taking a
step that was found (e.g. in `simp`) is reported. -/
partial def iWpAuto {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (lc : Nat) (lcIdx : Nat := 1)
    (simpFirst : Bool := true) (simpOnlyIf : Option Expr := none) :
    ProofModeM (Expr × Nat × Bool) := do
  let simpFirst ← if simpFirst then
      match simpOnlyIf with
      | some v => needsGooseSimp v
      | none => pure true
    else pure false
  if simpFirst then
    if let some (e', k) ← iWpExprSimp wp ehyps then
      let (pf, lc', _) ← iWpAuto hyps { wp with e := e' } lc lcIdx (simpFirst := false)
      return (← k pf, lc', true)
  if let some v ← wp.isVal? then
    let res ← IO.mkRef (lc, true)
    let pf ← iWpValue hyps wp v fun goal => do
      if let some wp' ← parseGooseWp? goal then
        let (pf, lc', _) ← iWpAuto hyps wp' lc lcIdx
        res.set (lc', true)
        return pf
      else addGoalCleaning hyps goal
    let (lc', p) ← res.get
    return (pf, lc', p)
  let saved ← saveState
  -- pure step
  if let some (st, hφ) ← observing? (iWpPureStepFind wp (failOnUnsolved := true) (multi := true)) then
    let ⟨_, hyps', e', k⟩ ← iWpPureStepTake hyps wp st hφ (lc := lc > 0)
    if e' == wp.e then
      saved.restore
    else if lc > 0 then
      -- introduce the credit: the new goal is `hyps' ⊢ £ 1 -∗ WP e'`
      let hT ← mkFreshTypeMVar
      let h ← mkFreshExprMVar hT
      let pf ← k h
      let T ← whnfR (← instantiateMVars hT)
      let wand ← whnfR T.getAppArgs.back!
      let lcProp := wand.getArg! 2
      let ivar ← mkFreshIVarId false
      let ⟨_, hyps'', hadd⟩ := hyps'.add bi (Name.mkSimple s!"Hlc{lcIdx}") ivar q(false) lcProp
      let (pf', lc', _) ← iWpAuto hyps'' { wp with e := e' } (lc - 1) (lcIdx + 1) (simpFirst := false)
      h.mvarId!.assign (← mkAppNamed ``tac_intro_hyp_wand
        [("hadd", hadd), ("Q", wp.mk' e' wp.Φ), ("!h", pf')])
      return (pf, lc', true)
    else
      let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx (simpFirst := false)
      return (← k pf', lc', true)
  -- load
  if let some ⟨_, hyps', e', k, vv⟩ ← observing? (iWpLoadStepV hyps wp) then
    let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx (simpOnlyIf := some vv)
    return (← k pf', lc', true)
  -- store (of a function literal: first rewrite it to `#(func.mk ..)`)
  if let some ⟨_, hyps', e', k⟩ ← observing? (iWpStoreStep hyps wp) then
    let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx (simpFirst := false)
    return (← k pf', lc', true)
  let extras := goose.wp.extras.get (← getOptions)
  if extras then
   if let some (e', k) ← iWpStoreFuncLit? wp ehyps then
    let (pf', lc', _) ← iWpAuto hyps { wp with e := e' } lc lcIdx (simpFirst := false)
    return (← k pf', lc', true)
  -- allocation of a local variable
  let res ← IO.mkRef lc
  let entered ← IO.mkRef false
  let saved ← saveState
  try
    let pf ← iWpAllocStep hyps wp (auto := true) none fun hyps' wp' => do
      entered.set true
      let (pf', lc', _) ← iWpAuto hyps' wp' lc lcIdx (simpFirst := false)
      res.set lc'
      return pf'
    return (pf, ← res.get, true)
  catch ex =>
    -- errors in the steps after the allocation are reported
    if ← entered.get then throw ex
    saved.restore
  -- a value constant (e.g. a package constant `def a : val := #(W64 3)`) blocks
  -- the next step: unfold it
  if extras then
   if let some (e', k) ← iWpUnfoldValConst? wp ehyps then
    let (pf', lc', _) ← iWpAuto hyps { wp with e := e' } lc lcIdx (simpFirst := true)
    return (← k pf', lc', true)
  -- done: clean up dead points-to facts
  let unused ← unusedPointsto hyps (wp.mk' wp.e wp.Φ)
  return (← addGoalCleaning hyps (wp.mk' wp.e wp.Φ), lc, !unused.isEmpty)

end auto

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_auto_lc n` is `wp_auto`, additionally producing `n` later credits
(`Hlc1 ... Hlcn`) from the first `n` pure steps; fails if not enough pure
steps were taken. -/
elab "wp_auto_lc " n:num : tactic =>
  runTacticGooseWp `wp_auto fun mvar g wp => do
    let (pf, lc, progress) ← iWpAuto g.hyps wp n.getNat
    unless progress do throwIPMError "no progress"
    if lc > 0 then throwIPMError "unable to generate enough later credits"
    mvar.assign pf

/-- `wp_auto` (Rocq `wp_auto`) repeatedly takes pure steps, loads (`wp_load`),
stores (`wp_store`) and allocations of local variables (`wp_alloc_auto`, which
names the location of `let: "x" := GoAlloc t #v` `x_ptr` and its points-to
`x`), stepping into the postcondition when the expression becomes a value.
At the end it clears the points-to facts of local variables that are no longer
used. Fails if no progress is made. -/
macro "wp_auto" : tactic => `(tactic| wp_auto_lc 0)

/-! ## `wp_apply` -/

/-! Specialization patterns of `wp_apply`. These are iris-lean's `specPat`s
without the `[H₁ … Hₙ] as name` form (naming the premise goal), whose `as` would
swallow the `as pats` of `wp_apply`. -/
declare_syntax_cat wpSpecPat
syntax ident : wpSpecPat
syntax "%" term:max : wpSpecPat
syntax "[" ("-")? (colGt ppSpace frameIdent)* (" //")? " ]" : wpSpecPat
syntax "[>" ("-")? (colGt ppSpace frameIdent)* (" //")? " ]" : wpSpecPat
syntax "[#" (colGt ppSpace frameIdent)* (" //")? " ]" : wpSpecPat
syntax "[" "$" "]" : wpSpecPat
syntax "[>" "$" "]" : wpSpecPat
syntax "[#" "$" "]" : wpSpecPat
syntax "(" pmTerm ")" : wpSpecPat

/-- The proof mode term of `wp_apply`: `lem $$ spat₁ … spatₙ`. -/
syntax wpPmTerm := term (colGt " $$ " (colGt ppSpace wpSpecPat)+)?

open Lean in
/-- Convert a `wpSpecPat` to the corresponding iris-lean `specPat`. -/
def wpSpecPatToSpecPat : TSyntax `wpSpecPat → MacroM (TSyntax `specPat)
  | `(wpSpecPat| $x:ident) => `(specPat| $x:ident)
  | `(wpSpecPat| % $t:term) => `(specPat| % $t)
  | `(wpSpecPat| [$[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?]) =>
    `(specPat| [$[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?])
  | `(wpSpecPat| [> $[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?]) =>
    `(specPat| [> $[-%$negTk]? $[$names:frameIdent]* $[//%$trivTk]?])
  | `(wpSpecPat| [# $[$names:frameIdent]* $[//%$trivTk]?]) =>
    `(specPat| [# $[$names:frameIdent]* $[//%$trivTk]?])
  | `(wpSpecPat| [$]) => `(specPat| [$])
  | `(wpSpecPat| [> $]) => `(specPat| [> $])
  | `(wpSpecPat| [# $]) => `(specPat| [# $])
  | `(wpSpecPat| ( $p:pmTerm )) => `(specPat| ( $p:pmTerm ))
  | _ => Macro.throwUnsupported

open Lean in
/-- Convert a `wpPmTerm` to an iris-lean `pmTerm`. -/
def wpPmTermToPmTerm (stx : TSyntax ``wpPmTerm) : MacroM (TSyntax `pmTerm) := do
  let t : Term := ⟨stx.raw[0]⟩
  let spats := stx.raw[1]
  if spats.isNone then return ← `(pmTerm| $t:term)
  let ps ← spats[1].getArgs.mapM fun p => wpSpecPatToSpecPat ⟨p⟩
  `(pmTerm| $t:term $$ $ps*)

section focus
open Lean Elab Tactic Meta Iris.ProofMode

/-- Run `tac` on the continuation goal of the last `wp_apply_raw` (the goal
tagged `wp_apply_cont`; failing that, the last Iris goal). Does nothing if there
is no such goal (e.g. the applied spec closed the goal). -/
elab "wp_focus_cont " tac:tactic : tactic => do
  let goals := (← getUnsolvedGoals).toArray
  let mut idx : Option Nat := none
  for h : i in [:goals.size] do
    if (← goals[i].getTag) == `wp_apply_cont then idx := some i
  if idx.isNone then
    for h : i in [:goals.size] do
      if isIrisGoal (← instantiateMVars (← goals[i].getType)) then idx := some i
  let some i := idx | return
  let g := goals[i]!
  let tagged := (← g.getTag) == `wp_apply_cont
  setGoals [g]
  evalTactic tac
  let gs' ← getUnsolvedGoals
  -- keep the tag on the (last Iris goal) resulting from the continuation
  if tagged then
    for g' in gs'.reverse do
      if isIrisGoal (← instantiateMVars (← g'.getType)) then
        g'.setTag `wp_apply_cont
        break
  setGoals (goals.toList.take i ++ gs' ++ goals.toList.drop (i + 1))

end focus

/-- `wp_apply lem $$ spats as pats` (Rocq `wp_apply (lem with "spats") as "pats"`):
`wp_apply_core lem $$ spats`, then solve `is_pkg_init` premises (`iPkgInit`),
introduce `pats` in the continuation, and run `wp_auto` on it (`--no-auto`
disables this; `--lc n` makes `wp_auto` produce `n` credits). `with` is
accepted for `as`.

The continuation is the goal whose conclusion is the WP of the rest of the
program (tagged by `wp_apply_raw`), even when side goals come after it; if the
applied spec closes the goal, `as`/`wp_auto` are skipped. If the spec does not
apply, `wp_pures` is run first and it is tried again (e.g. for a call whose
argument is still `Pair (Val _) (Val _)`). To apply an Iris hypothesis `IH` with
Lean arguments, pass them as pure spec patterns: `wp_apply IH $$ %x %y [H]`.
The spec patterns are
iris-lean's, except that `[H] as name` (naming a premise goal) is not
available, so that `wp_apply lem $$ [H] as pats` introduces `pats`. -/
syntax wpNoAuto := " --no-auto"
syntax wpLc := " --lc " num
syntax wpAs := (" as " <|> " with ") (colGt ppSpace introPat)+

syntax (name := wpApply) "wp_apply " wpPmTerm (wpNoAuto)? (wpLc)? (wpAs)? : tactic

macro_rules
  | `(tactic| wp_apply $wpmt:wpPmTerm $[$na:wpNoAuto]? $[$lc:wpLc]? $[$as?:wpAs]?) => do
    let pmt ← wpPmTermToPmTerm wpmt
    let intro : Lean.TSyntax `tactic ←
      match as? with
      | some a =>
        let pats : Lean.TSyntaxArray `introPat := a.raw[1].getArgs.map (⟨·⟩)
        `(tactic| wp_focus_cont (iintro $pats*))
      | none => `(tactic| skip)
    let n : Lean.TSyntax `num := match lc with
      | some l => ⟨l.raw[1]⟩
      | none => Lean.Syntax.mkNumLit "0"
    let auto : Lean.TSyntax `tactic ←
      if na.isSome then `(tactic| skip)
      else `(tactic| wp_focus_cont (try wp_auto_lc $n))
    let core ← `(tactic| focus ((first | wp_apply_raw $pmt | (wp_pures; wp_apply_raw $pmt)) <;> wp_apply_post))
    `(tactic| focus (($core:tactic) <;> (try iPkgInit); $intro:tactic; $auto:tactic; wp_untag_cont))

/-! ## Boolean cleanup -/

section bool_lemmas
variable [ffi_syntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
  [go.PreSemantics]

theorem true_neq_false : (#true : val) ≠ #false := fun h =>
  absurd (go.into_val_inj h) (by decide)
theorem false_neq_true : (#false : val) ≠ #true := fun h =>
  absurd (go.into_val_inj h) (by decide)

theorem if_decide_bool_eq_true {A : Type _} (P : Prop) [Decidable P] (x y : A) :
    (if decide ((#(decide P) : val) = #true) then x else y) = (if decide P then x else y) := by
  by_cases h : P <;> simp [h, false_neq_true]

theorem if_decide_bool_eq_false {A : Type _} (P : Prop) [Decidable P] (x y : A) :
    (if decide ((#(decide P) : val) = #false) then x else y) = (if decide P then y else x) := by
  by_cases h : P <;> simp [h, true_neq_false]

theorem if_decide_eq {A : Type _} (b : Bool) (x y : A) :
    (if decide ((#b : val) = #b) then x else y) = x := by simp

theorem if_decide_true_eq_false {A : Type _} (x y : A) :
    (if decide ((#true : val) = #false) then x else y) = y := by simp [true_neq_false]

theorem if_decide_false_eq_true {A : Type _} (x y : A) :
    (if decide ((#false : val) = #true) then x else y) = y := by simp [false_neq_true]

end bool_lemmas

/-- Rocq `cleanup_bool_decide`. -/
macro "cleanup_bool_decide" : tactic => `(tactic|
  try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, if_decide_eq,
    if_decide_true_eq_false, if_decide_false_eq_true, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte, ite_true, ite_false])

/-! ## Conditionals -/

section if_destruct
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Find a `decide p` (or `#b` for a Boolean variable `b`) in the WP expression. -/
def findIfCond (e : Expr) : MetaM (Option (Sum Expr Expr)) := do
  let e ← instantiateMVars e
  if let some d := e.find? (fun s => s.isAppOfArity ``Decidable.decide 2 && !s.hasLooseBVars) then
    return some (.inl (d.getArg! 0))
  if let some b := e.find? (fun s =>
      s.isAppOfArity ``GoGlobalContext.into_val 4 && (s.getArg! 2).isConstOf ``Bool &&
        (s.getArg! 3).isFVar) then
    return some (.inr (b.getArg! 3))
  return none

/-- `#(decide P) = #b` (for a literal `b`) becomes `P`; other propositions are
unchanged. -/
def peelDecideEq (p : Expr) : MetaM Expr := do
  let p ← instantiateMVars p
  let_expr Eq _ a b := p | return p
  let a := a.consumeMData
  let b ← whnfR b
  unless a.isAppOfArity ``GoGlobalContext.into_val 4 && b.isAppOfArity ``GoGlobalContext.into_val 4 do
    return p
  let x := (a.getArg! 3).consumeMData
  let lit := (← whnfR (b.getArg! 3))
  unless lit.isConstOf ``Bool.true || lit.isConstOf ``Bool.false do return p
  if x.isAppOfArity ``Decidable.decide 2 then return x.getArg! 0
  return p

/-- The condition of the `if:` at the head of the WP expression: the `If c _ _`
in evaluation position whose condition `c` is a value (the next redex), or else
the outermost `If` in evaluation position. -/
def findHeadIf (e : Expr) : MetaM (Option Expr) := do
  let mut outer : Option Expr := none
  for (_, e') in ← allEctx e do
    let e' ← whnfR (← instantiateMVars e')
    let_expr Perennial.expr.If _ c _ _ := e' | continue
    if (← isGooseVal? c).isSome then return some c
    if outer.isNone then outer := some c
  return outer

end if_destruct

set_option hygiene false in
open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Rocq `wp_if_destruct`: case split on the condition of the `if:` at the head
of the WP expression — the first `decide P` (or Boolean variable `#b`) in it
(if there is no such `if:`, the first one in the expression, then in the whole
goal) — then `wp_pures`, `cleanup_bool_decide` and `wp_auto`. The case
hypothesis is `Hif` (accessible: the tactic is unhygienic).

Unlike earlier versions, a `decide` elsewhere in the expression (e.g. in a loop
postcondition) is not picked when there is an `if:` at the head. -/
elab "wp_if_destruct" : tactic => do
  let some g := parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "wp_if_destruct: not in the Iris proof mode"
  let target ← match ← parseGooseWp? g.goal with
    | some wp => Pure.pure wp.e
    | none => Pure.pure g.goal
  -- the condition of the `if:` at the head of the expression; then (as before)
  -- anywhere in the expression, then anywhere in the goal
  let headCond ← match ← findHeadIf target with
    | some c => match ← findIfCond c with
      | some (.inl p) => Pure.pure (some (.inl (← peelDecideEq p)))
      | r => Pure.pure r
    | none => Pure.pure none
  let cond ← match headCond with
    | some c => Pure.pure (some c)
    | none => match ← findIfCond target with
      | some c => Pure.pure (some c)
      | none => findIfCond g.goal
  match cond with
  | some (.inl p) =>
    let pStx ← Term.exprToSyntax p
    evalTactic (← `(tactic| by_cases Hif : $pStx))
    -- the positive case rewrites with `decide_eq_true Hif`, the negative one with
    -- `decide_eq_false Hif` (trying both in each case could rewrite the wrong way)
    let post ← `(tactic| ((try subst Hif); wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide))
    match ← getGoals with
    | gPos :: gNeg :: rest =>
      setGoals [gPos]
      evalTactic (← `(tactic| ((try simp only [decide_eq_true Hif, ↓reduceIte]); $post:tactic)))
      let r1 ← getGoals
      setGoals [gNeg]
      evalTactic (← `(tactic| ((try simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte]); $post:tactic)))
      setGoals (r1 ++ (← getGoals) ++ rest)
    | _ => throwError "wp_if_destruct: by_cases did not produce two goals"
  | some (.inr b) =>
    let bStx ← Term.exprToSyntax b
    evalTactic (← `(tactic| cases $bStx:term))
    evalTactic (← `(tactic| all_goals (
      wp_pures;
      cleanup_bool_decide;
      (try wp_auto);
      cleanup_bool_decide)))
  | none => throwError "wp_if_destruct: no `decide` or Boolean variable in the expression"

/-! ## Struct instances -/

/-- Rocq `solve_into_val_typed_struct`: prove `IntoValTypedUnderlying V T` for
a struct type `T` whose typed points-to is the conjunction of its (named)
field points-tos. -/
macro "solve_into_val_typed_struct" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typed_pointsto_unseal, typed_pointsto_wrap]
  · intro s E t _ v
    iintro %Φ _ HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    wp_apply wp_GoPrealloc as %l %Hnotnull
    repeat (wp_if_destruct; (rotate_left; wp_apply_core wp_AngelicExit))
    iapply HΦ
    try simp only [TypedPointsto.typed_pointsto_def, named]
    iframe
    ipureintro; (try simp only [and_self]); exact Hnotnull
  · intro s E t _ l dq v
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    try simp only [TypedPointsto.typed_pointsto_def]
    iNamed Hl
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    try wp_auto
    cases v
    try simp only
    iapply HΦ
    try simp only [TypedPointsto.typed_pointsto_def, named]
    iframe
    ipureintro; (try simp only [and_self]); exact Hnn
  · intro s E t _ l v w
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    try simp only [TypedPointsto.typed_pointsto_def]
    iNamed Hl
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    try wp_auto
    cases w
    iapply HΦ
    try simp only [TypedPointsto.typed_pointsto_def, named]
    iframe
    ipureintro; (try simp only [and_self]); exact Hnn
  · infer_instance))

instance equals_unfold_nil (A : Type) : EqualsUnfold (@List.nil A) (@List.nil A) := ⟨rfl⟩

section into_val_typed_unit
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance into_val_typed_unit : IntoValTypedUnderlying (GF := GF) Unit (go.StructType []) := by
  solve_into_val_typed_struct

end into_val_typed_unit

/-! ## Loops -/

/-- Rocq `wp_for`: apply `wp_for` to the loop at the head of the goal with the
current context as invariant (see `wp_for_core`), then clean up. `wp_for H`
additionally destructs `H` with `iNamed`. -/
syntax "wp_for" (ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| wp_for) => `(tactic| (wp_for_core; (try wp_auto); cleanup_bool_decide; (try wp_auto)))
  | `(tactic| wp_for $h:ident) =>
    `(tactic| (wp_for_core; iNamed $h:ident; (try wp_auto); cleanup_bool_decide; (try wp_auto)))

/-- Rocq `wp_for_post`: prove a `for_postcondition` goal (see
`wp_for_post_core`), then `wp_auto`. -/
macro "wp_for_post" : tactic => `(tactic| (wp_for_post_core; (try wp_auto)))

open Lean Elab Tactic Meta Iris.ProofMode in
set_option hygiene false in
/-- Internal: `iapply HΦ` (or `iapply HPost` when there is no `HΦ`), reporting
the error of `iapply` itself (e.g. a postcondition that does not match because of
a stuck `Convert`) rather than "unknown identifier `HPost`". -/
elab "wp_end_apply" : tactic => do
  let some g := parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "wp_end: not in the Iris proof mode"
  let names := (hypsList g.hyps).map (·.1)
  let hasΦ := names.contains `HΦ
  let hasPost := names.contains `HPost
  if !hasΦ && !hasPost then
    throwError "wp_end: no continuation hypothesis `HΦ` or `HPost` in the Iris context"
  if hasΦ then
    let saved ← saveState
    try
      evalTactic (← `(tactic| iapply HΦ))
      return
    catch ex =>
      unless hasPost do throw ex
      saved.restore
  evalTactic (← `(tactic| iapply HPost))

set_option hygiene false in
/-- Rocq `wp_end`: finish a function proof by applying the continuation `HΦ`
(or `HPost`) and trying to discharge the remaining goal. If applying the
continuation fails, the error of `iapply` is reported. -/
macro "wp_end" : tactic => `(tactic| (
  wp_pures
  repeat imodintro
  wp_end_apply;
  (try (first
    | (iframe; done)
    | itrivial
    | (ipureintro; trivial)
    | (iframe; ipureintro; trivial)))))

end Perennial
