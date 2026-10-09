/-
The user-facing automation.

* `wp_start` / `wp_start as pat` / `wp_start_folded as pat`: begin the proof of
  a Texan triple for a function or method.
* `wp_func_call`, `wp_method_call`: unfold `#(functions f ts)` /
  `#(methods t m v)` with the `FuncUnfold`/`MethodUnfold` instances.
* `wp_auto`, `wp_auto_lc n`: repeatedly take pure steps, loads, stores and
  allocations of local variables, then drop points-to facts of dead locals.
* `wp_apply lem $$ spats as pats`: apply a spec (see `wp_apply_core`), solve
  `isPkgInit` premises, introduce `pats` in the continuation and run
  `wp_auto` (`wp_apply +noauto` disables this; `wp_apply (lc := n)` asks for
  `n` later credits).
* `wp_if_destruct`, `wp_for`, `wp_for hyp`, `wp_for_post`, `wp_end`.

Details:
* `wp_apply ... as %x Hx` uses iris-lean intro patterns (`with` is accepted as
  a synonym of `as`). Lean-level binders are introduced with `%x`. The spec patterns of `wp_apply` are
  iris-lean's minus `[H] as name`, so `wp_apply lem $$ [H] as pats` works.
* To skip `wp_auto` after `wp_apply`, use `wp_apply +noauto`. The options
  `--no-auto`/`--lc n` would be Lean comments and are rejected with an error.
* `wp_start` names the `isPkgInit` facts it moves to the intuitionistic
  context `Hpkg`, `Hpkg2`, ....
* `wp_if_destruct` names the case hypothesis `Hif`
  and substitutes it when it is an equation between a variable and a
  non-variable term (`x = W64 0`); equations between two variables are kept. It
  splits on the condition of the `if:` at the head of the expression.
* All WP tactics fail (instead of leaving a `sorry`) when a term does not
  elaborate (`withNoSorry`).
* With `goose.wp.extras` (on by default; `set_option goose.wp.extras false`
  for proofs that do these steps by hand): `wp_auto` rewrites
  stored function literals to `#(func.mk ..)` and unfolds package constants
  (`def a : val := #..`) that block a step; `wp_pures`/`wp_auto` stop at slice
  composite literals (use `wp_slice_literal`), reduce `match`es on
  definitions of constructors, and use the `goose_wp_simp_extra` simp set
  (`Perennial/Golang/Theory/TacticsSimp.lean`).
* `wp_func_call` only rewrites the WP expression (not the hypotheses), and (with
  `goose.wp.extras`) finds `FuncUnfold f (List.replicate n t)` instances for type
  arguments `[t, .., t]`.
* `wp_alloc_auto` (not `wp_auto`) also does anonymous allocations.
-/
module

public import Perennial.Golang.Theory.Pkg
public import Perennial.Golang.Theory.Loop
public import Perennial.Golang.Theory.Assume
public import Perennial.Golang.Theory.Mem
public import Perennial.Golang.Theory.Predeclared
public import Perennial.Golang.Theory.ArrayLit

@[expose] public section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## Function and method calls -/

section func_call
open Lean Elab Tactic Meta Qq Iris.ProofMode

theorem tac_wp_func_unfold {PROP : Type _} [BI PROP] {Δ P Q : PROP} (h : Δ ⊢ Q) (heq : P = Q) :
    Δ ⊢ P := heq ▸ h

/-- `[t, t, ..., t]` (`n` copies), as `(n, t)`. -/
meta partial def replicateLit? (ts : Lean.Expr) (t? : Option Lean.Expr := none) (n : Nat := 0) :
    MetaM (Option (Nat × Lean.Expr)) := do
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
meta def funcUnfoldEq (fv : Lean.Expr) (f ts : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let valTy ← inferType fv
  let tryInst (ts' : Lean.Expr) : MetaM (Option Lean.Expr) := do
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
meta def findFuncCall (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let isFn (fv : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
    let fv := (← instantiateMVars fv).consumeMData
    unless fv.isAppOfArity ``GoGlobalContext.intoVal 4 do return none
    let x ← whnfR (fv.getArg! 3)
    unless x.isAppOfArity ``functions 6 || x.getAppFn.constName? == some ``functions do return none
    let args := x.getAppArgs
    if args.size < 2 then return none
    return some (fv, args[args.size - 2]!, args[args.size - 1]!)
  let mut found := none
  for (_, e') in ← allEctx e do
    let e' ← whnfR e'
    let_expr Perennial.Expr.App _ fe _ := e' | continue
    let some fv ← isGooseVal? fe | continue
    if let some r ← isFn fv then found := some r
  if found.isSome then return found
  let some fv := (← instantiateMVars e).find? (fun s =>
      s.isAppOfArity ``GoGlobalContext.intoVal 4 &&
        (s.getArg! 3).getAppFn.constName? == some ``functions) | return none
  isFn fv

end func_call

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- The core of `wp_func_call`; `false` if no call was found. -/
meta def wpFuncCallCore : TacticM Bool :=
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
      [("PROP", g.prop), ("Δ", g.e), ("P", g.goal), ("Q", wpE'.mk' e' wp.Φ), ("!h", pf),
       ("!heq", heq')])
    return true

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_func_call`: unfold the function value `#(functions f ts)` of the next
call in the WP expression (see `findFuncCall`) with its `FuncUnfold` instance
(with `goose.wp.extras`, also for type arguments `[t, ..., t]` matching an
meta instance for `List.replicate n t`), then try to solve `isPkgInit` goals. Only the WP
expression is rewritten (all occurrences of that function value in it), not the
hypotheses. Falls back to `rw [func_unfold]`. -/
elab "wp_func_call" : tactic => do
  let saved ← saveState
  let done ← try wpFuncCallCore catch _ => pure false
  unless done do
    saved.restore
    evalTactic (← `(tactic| rw [func_unfold]))
  evalTactic (← `(tactic| try iPkgInit))

/-- `wp_method_call`: rewrite `#(methods t m v)` with its `MethodUnfold`
instance and try to solve `isPkgInit` goals. -/
macro "wp_method_call" : tactic => `(tactic| (rw [method_unfold]; (try iPkgInit)))

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Is `e` (up to `named`) `isPkgInit _`? -/
meta def isPkgInitProp (e : Lean.Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  return e.isAppOfArity ``isPkgInit 4

/-- Move the `isPkgInit` conjuncts at the front of
`H` to the intuitionistic context. Returns `false` if `H` was entirely an
`isPkgInit` (and is now gone). -/
meta partial def destructPkgInit (h : Name) : TacticM Bool := withMainContext do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return true
  let some (_, ty) := g.hyps.find? h | return false
  -- the `isPkgInit` facts are named `Hpkg`, `Hpkg2`, ... (unless taken)
  let names := (hypsList g.hyps).map (·.1)
  let pkgName := (List.range 100).findSome? (fun i =>
    let n := if i == 0 then `Hpkg else Name.mkSimple s!"Hpkg{i + 1}"
    if names.contains n then none else some n) |>.getD `Hpkg
  let pkgId := mkIdent pkgName
  let ty' ← whnfR (← instantiateMVars ty)
  if ty'.isAppOfArity ``BIBase.sep 4 then
    if ← isPkgInitProp (ty'.getArg! 2) then
      evalTactic (← `(tactic| icases $(mkIdent h):ident with ⟨#$pkgId:ident, $(mkIdent h):ident⟩))
      return ← destructPkgInit h
    return true
  if ← isPkgInitProp ty' then
    evalTactic (← `(tactic| icases $(mkIdent h):ident with #$pkgId:ident))
    return false
  if ty'.isAppOfArity ``BIBase.emp 2 then
    evalTactic (← `(tactic| iclear $(mkIdent h):ident))
    return false
  return true

/-- The fields `(isPkgInitDeps, isPkgInitDef)` of an `IsPkgInit`
instance, obtained by unfolding the instance constant (e.g. one built with
`define_is_pkg_init`) to an `IsPkgInit.mk` application. -/
meta partial def pkgInitInstFields (inst : Lean.Expr) (fuel : Nat := 20) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let inst := (← instantiateMVars inst).headBeta
  if inst.isAppOfArity ``IsPkgInit.mk 5 then return some (inst.getArg! 3, inst.getArg! 4)
  if fuel == 0 then return none
  match ← unfoldDefinition? inst with
  | some i => pkgInitInstFields i (fuel - 1)
  | none => return none

/-- In the conclusion of the Iris goal, unfold `isPkgInit pkg` into
`□ deps ∗ □ P`, where `deps`/`P` are the fields of the
`IsPkgInit` instance (so the dependencies appear as `isPkgInit dep ∗ ... ∗ True`).
The change is definitional (checked by the kernel). -/
elab "isPkgInit_unfold" : tactic => do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let some #[prop, bi, P, Q] := t.consumeMData.appM? ``Entails'
    | throwError "isPkgInit_unfold: not an Iris goal"
  let Q' ← Meta.transform Q (pre := fun e => do
    if e.isAppOfArity ``isPkgInit 4 then
      let some (deps, d) ← pkgInitInstFields (e.getArg! 3) | return .continue
      let pkg := e.getArg! 2
      let body ← mkAppOptM ``isPkgInitWrap #[e.getArg! 0, e.getArg! 1, pkg, e.getArg! 3]
      let some body ← unfoldDefinition? body | return .continue
      let body ← Meta.transform body (pre := fun x => do
        if x.isAppOfArity ``IsPkgInit.isPkgInitDeps 4 && x.getArg! 2 == pkg then return .done deps
        if x.isAppOfArity ``IsPkgInit.isPkgInitDef 4 && x.getArg! 2 == pkg then return .done d
        if x.isAppOfArity ``named 3 then return .visit (x.getArg! 2)
        return .continue)
      return .done body
    return .continue)
  let t' := mkApp4 t.consumeMData.getAppFn prop bi P Q'
  replaceMainGoal [← g.replaceTargetDefEq t']

end tactics

/-- `wp_start_folded as pat`: introduce `Φ`, the precondition `Hpre` and
the continuation `HΦ` of a Texan triple; move `isPkgInit` facts of the
precondition to the intuitionistic context; destruct the rest with `pat`.
Does not unfold the function being called. -/
syntax "wp_start_folded" (" as " icasesPat)? : tactic

open Lean Elab Tactic in
set_option hygiene false in
elab_rules : tactic
  | `(tactic| wp_start_folded $[as $pat?]?) => do
    evalTactic (← `(tactic| try imodintro))
    -- an old `Φ` (e.g. of an enclosing proof) is cleared rather than
    -- shadowed, if it is not used
    evalTactic (← `(tactic| try clear Φ))
    evalTactic (← `(tactic| iintro %Φ Hpre HΦ))
    let present ← destructPkgInit `Hpre
    if present then
      if let some pat := pat? then
        evalTactic (← `(tactic| icases Hpre with $pat))

/-- `wp_start as pat`: `wp_start_folded as pat`, then unfold the function
(`wp_func_call`) or method (`wp_method_call`) being called and take the call
steps (`wp_call`). `wp_start` keeps the precondition as `Hpre`. -/
syntax "wp_start" (" as " icasesPat)? : tactic

macro_rules
  | `(tactic| wp_start as $p:icasesPat) =>
    `(tactic| (wp_start_folded as $p; (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)))
  | `(tactic| wp_start) =>
    `(tactic| (wp_start_folded; (try (first | wp_func_call | (wp_method_call; (try wp_call)))); (try wp_call)))

/-- Finish the proof of a package's `wp_initialize'`: unfold `isPkgInit`
in the goal (`isPkgInit_unfold`) and frame the dependencies' `isPkgInit`
facts from the intuitionistic context. -/
macro "is_pkg_init_finish" : tactic => `(tactic| (
  isPkgInit_unfold
  (try imodintro)
  (try iframe #)
  (try (imodintro; itrivial))
  (try itrivial)))

/-! ## `if:` with an angelic `else` branch -/

section if_angelic
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- `if: #(decide P) then e else AngelicExit #()`: the `else` branch proves
anything, so it suffices to prove the `then` branch assuming `P`. -/
theorem tac_wp_if_angelic {P : Prop} [Decidable P] {K : List EctxItem} {e : Expr}
    {Δ : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (h : Δ ⊢ iprop(⌜P⌝ -∗ WP (fill K e) @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K (If (Val #(decide P)) e (App (Val (GoInstruction AngelicExit)) (Val #()))))
      @ s; E {{ Φ }} := by
  by_cases hP : P
  · rw [decide_eq_true hP]
    iintro HΔ
    wp_pure
    iapply h $$ HΔ
    ipureintro; exact hP
  · rw [decide_eq_false hP]
    iintro -
    wp_pure
    wp_bind (App (Val (GoInstruction AngelicExit)) (Val #()))
    iapply wp_AngelicExit

/-- `tac_wp_if_angelic` with the hypothesis in the Lean context. -/
theorem tac_wp_if_angelic' {P : Prop} [Decidable P] {K : List EctxItem} {e : Expr}
    {Δ : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (h : P → Δ ⊢ WP (fill K e) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (If (Val #(decide P)) e (App (Val (GoInstruction AngelicExit)) (Val #()))))
      @ s; E {{ Φ }} :=
  tac_wp_if_angelic (by iintro HΔ %hp; iapply (h hp); iexact HΔ)

end if_angelic

section if_angelic_find
open Lean Meta Iris.ProofMode

/-- The head `if: #(decide P) then e else AngelicExit #()` of a WP expression:
`(P, e)` and its evaluation context. -/
meta def findAngelicIf (e : Lean.Expr) : ProofModeM (Option ((Lean.Expr × Lean.Expr) × List Lean.Expr × Lean.Expr)) :=
  findEctx e (fun _ e => do
    let e ← whnfR e
    let_expr Perennial.Expr.If _ c e1 e2 := e | throwError "no"
    let some cv ← isGooseVal? c | throwError "no"
    let cv := (← instantiateMVars cv).consumeMData
    unless cv.isAppOfArity ``GoGlobalContext.intoVal 4 do throwError "no"
    let d ← whnfR (cv.getArg! 3)
    unless d.isAppOfArity ``Decidable.decide 2 do throwError "no"
    let e2 ← whnfR e2
    let_expr Perennial.Expr.App _ f a := e2 | throwError "no"
    let some fv ← isGooseVal? f | throwError "no"
    let fv ← whnfR fv
    unless fv.isAppOf ``Perennial.val.GoInstruction do throwError "no"
    unless (fv.getArg! 1).isAppOf ``GoInstruction.AngelicExit do throwError "no"
    let some _ ← isGooseVal? a | throwError "no"
    return (d.getArg! 0, e1))


end if_angelic_find

/-! ## `wp_auto` -/

section auto
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Hypotheses `l ↦{dq} v` whose location `l` is the cell `x_ptr` of a Go local
variable that occurs nowhere else. -/
meta def unusedPointsto {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Lean.Expr) : MetaM (List (IVarId × FVarId)) := do
  let goal ← instantiateMVars goal
  if goal.hasExprMVar then return []
  let hs := hypsList hyps
  let mut res := []
  for (_, ivar, p, ty) in hs do
    if isTrue p then continue
    let ty ← instantiateMVars ty
    unless ty.isAppOfArity ``typedPointsto 6 do continue
    let l := ty.getArg! 3
    let .fvar lid := l | continue
    -- only the cells of Go local variables (named `x_ptr` by `wp_alloc_auto`):
    -- a location obtained otherwise (e.g. from a spec) may still be needed, e.g.
    -- for a postcondition `∃ l, l ↦ v`
    let some ldecl := (← getLCtx).find? lid | continue
    unless ldecl.userName.eraseMacroScopes.toString.endsWith "_ptr" do continue
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
meta def addGoalCleaning {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Lean.Expr) : ProofModeM Lean.Expr :=
  -- remove the closedness annotations of `wp_auto` first
  addBIGoalStripped hyps goal (addGoalCleaningCore hyps)
where addGoalCleaningCore {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (goal : Lean.Expr) :
    ProofModeM Lean.Expr := do
  let unused ← unusedPointsto hyps goal
  if unused.isEmpty then return ← addBIGoal hyps goal
  -- remove the hypotheses one by one, building the proof (newest first: `unused` is in
  -- context order, and removing the last hypothesis of the context is `O(1)`, while
  -- removing the first one rebuilds the context)
  let rec go {ehyps : Q($prop)} (hyps : Hyps bi ehyps) (us : List (IVarId × FVarId)) :
      ProofModeM Lean.Expr := do
    match us with
    | [] => addBIGoalWithoutFVars (u := u) hyps goal (unused.map (·.2)).toArray
    | (ivar, _) :: us =>
      let r := hyps.remove false ivar
      let pf ← go r.hyps' us
      mkAppNamed ``tac_clear_hyp
        [("PROP", prop), ("Δ", ehyps), ("Δ'", r.e'), ("P", r.out), ("Q", goal), ("h", r.pf),
         ("!h'", pf)]
  go hyps unused.reverse

/-- `wp_auto_lc`: repeatedly take pure steps (the first `lc` of them
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
continuation proof (`iWpAllocStep`); the proof terms of the steps are built
without unification (`mkAppNamedDirect?`); structural steps (`rec`, beta, pairs)
get their `PureWp` instance directly and the other searches are shared between
redexes of the same shape (`synthPureWp`); a redex deep inside its evaluation
context is focused on (`GooseWpGoal.focus?`); the continuations and their
closedness proofs, which are shared below the binders of the allocations, are
`let`-bound once at the top of the proof (`assignHoisted`; otherwise the declaration
stores and the kernel checks a copy per binder depth). Together these make
`wp_auto` roughly linear in the length of straight-line code and in the depth of
evaluation contexts.

Only the search for the next step may fail silently; an error while taking a
step that was found (e.g. in `simp`) is reported. -/
meta partial def iWpAuto {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (lc : Nat) (lcIdx : Nat := 1)
    (simpFirst : Bool := true) (simpOnlyIf : Option Lean.Expr := none) (allowFocus : Bool := true) :
    ProofModeM (Lean.Expr × Nat × Bool) := do
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
      let goal := (← popNestedPost? wp goal).getD goal
      if let some wp' ← parseGooseWp? goal then
        let (pf, lc', _) ← iWpAuto hyps wp' lc lcIdx
        res.set (lc', true)
        return pf
      else addGoalCleaning hyps goal
    let (lc', p) ← res.get
    return (pf, lc', p)
  -- a redex deep inside its evaluation context: focus on it (see `wpNestedPost`)
  if allowFocus then
    if let some (wp', k) ← wp.focus? ehyps then
      let (pf, lc', p) ← iWpAuto hyps wp' lc lcIdx (simpFirst := false)
      return (← k pf, lc', p)
  -- a run of `let:`s of values: step through it at once
  if lc == 0 then
    if let some (some ⟨_, hyps', e', k⟩) ← observing? (iWpLetRun? hyps wp) then
      let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx (simpFirst := false)
      return (← k pf', lc', true)
  let saved ← saveState
  -- pure step
  if let some (st, hφ) ← observing? (iWpPureStepFind wp (failOnUnsolved := true) (multi := true)) then
    let ⟨ehyps1, hyps', e', k⟩ ← iWpPureStepTake hyps wp st hφ (lc := lc > 0)
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
      let ⟨ehyps'', hyps'', hadd⟩ :=
        hyps'.add bi (Name.mkSimple s!"Hlc{lcIdx}") ivar q(false) lcProp
      let (pf', lc', _) ← iWpAuto hyps'' { wp with e := e' } (lc - 1) (lcIdx + 1) (simpFirst := false)
      h.mvarId!.assign (← mkAppNamed ``tac_intro_hyp_wand
        [("PROP", prop), ("Δ", ehyps1), ("Δ'", ehyps''), ("Q", wp.mk' e' wp.Φ), ("P", lcProp),
         ("hadd", hadd), ("!h", pf')])
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
  let res0 ← IO.mkRef lc
  -- (`solve_into_val_typed_struct`) an `if:` with an angelic `else` branch
  if ← autoAngelicIf.get then
    if let some ((P, e1), K, _) ← findAngelicIf wp.e then
      binderSteps.modify (· + 1)
      let pf ← withLocalDeclD (← mkFreshUserName `Hif) P fun h => do
        let (pf', lc', _) ← iWpAuto hyps { wp with e := ← fillExpr K e1 } lc lcIdx
        res0.set lc'
        mkLambdaFVars #[h] pf'
      return (← wp.mkAppNamed ``tac_wp_if_angelic'
        [("P", P), ("K", wp.quoteK K), ("e", e1), ("Δ", ehyps), ("s", wp.s), ("E", wp.E),
         ("Φ", wp.Φ), ("!h", pf)], ← res0.get, true)
  -- a call of an implementation constant `«Fooⁱᵐᵖˡ» v` (e.g. after
  -- `wp_method_call`): take the beta step
  if extras then
    let saved ← saveState
    if let some ⟨_, hyps', e', k⟩ ← observing? (iWpCallStep hyps wp (onlyImpl := true)) then
      let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx (simpFirst := false)
      return (← k pf', lc', true)
    saved.restore
  -- no step in the focused expression: unfocus, and try the steps on the whole
  -- expression (as without focusing)
  if let some (wp', k) ← wp.unfocus? ehyps then
    let (pf, lc', p) ← iWpAuto hyps wp' lc lcIdx (simpFirst := false) (allowFocus := false)
    return (← k pf, lc', p)
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
    -- annotate the continuations with their free variables (see `fvClosed`)
    fvCache.set {}; closedCache.set {}; hoistCandidates.set #[]; binderSteps.set 0
    let eA ← if goose.wp.fvAnnot.get (← getOptions) then annotateFv wp.ext wp.e else pure wp.e
    let (pf, lc, progress) ← iWpAuto g.hyps { wp with e := eA } n.getNat
    let pf ← if eA == wp.e then pure pf else
      let heq ← mkExpectedTypeHint (← mkEqRefl (wp.wrap wp.e)) (← mkEq (wp.wrap wp.e) (wp.wrap eA))
      wp.mkAppNamed ``tac_wp_expr_simp
        [("Δ", g.e), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e), ("e'", wp.wrap eA),
         ("!h", pf), ("!heq", heq)]
    fvCache.set {}; closedCache.set {}
    unless progress do throwIPMError "no progress"
    if lc > 0 then throwIPMError "unable to generate enough later credits"
    let cands ← hoistCandidates.get
    hoistCandidates.set #[]
    assignHoisted mvar pf cands (← getThe ProofModeM.State).goals

/-- `wp_auto` repeatedly takes pure steps, loads (`wp_load`),
stores (`wp_store`) and allocations of local variables (`wp_alloc_auto`, which
names the location of `let: "x" := GoAlloc t #v` `x_ptr` and its points-to
`x`), stepping into the postcondition when the expression becomes a value.
At the end it clears the points-to facts of local variables that are no longer
used. Fails if no progress is made. -/
macro "wp_auto" : tactic => `(tactic| wp_auto_lc 0)

open Lean Elab Tactic in
/-- Internal (`solve_into_val_typed_struct`): `wp_auto`, also taking the steps
`if: #(decide P) then e else AngelicExit #()` (with an inaccessible hypothesis
`P`). -/
elab "wp_auto_angelic" : tactic => do
  let saved ← autoAngelicIf.get
  autoAngelicIf.set true
  try evalTactic (← `(tactic| wp_auto)) finally autoAngelicIf.set saved

/-! ## `wp_apply` -/

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Rewrite the function literal values `RecV f x e` in the WP expression to Go
function values `#(func.mk f x e)` (`recv_eq_func_mk`), so that specs taking a
`GoFunc` argument (e.g. `wp_mapInsert`, or a function with a callback
parameter) apply. Fails if there is none. `wp_apply` tries this when the spec
does not apply. -/
elab "wp_func_lits" : tactic =>
  runTacticGooseWp `wp_func_lits fun mvar g wp => do
    unless (wp.e.find? (·.isAppOfArity ``Perennial.val.RecV 4)).isSome do
      throwIPMError "no function literal in the expression"
    let thms ← ({} : SimpTheorems).addConst ``recv_eq_func_mk
    let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
    let ⟨res, _⟩ ← Meta.simp wp.e ctx
    let some p := res.proof? | throwIPMError "no function literal in the expression"
    let heq ← wp.wrapEq res.expr (some p)
    let pf ← addBIGoal g.hyps (wp.mk' res.expr wp.Φ)
    mvar.assign (← wp.mkAppNamed ``tac_wp_expr_simp
      [("Δ", g.e), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e),
       ("e'", wp.wrap res.expr), ("!h", pf), ("!heq", heq)])

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
meta def wpSpecPatToSpecPat : TSyntax `wpSpecPat → MacroM (TSyntax `specPat)
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
meta def wpPmTermToPmTerm (stx : TSyntax ``wpPmTerm) : MacroM (TSyntax `pmTerm) := do
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

/-- Simplify the types of the Iris hypotheses `ivars` with the `goose_wp_simp`
simp set(s), so that they are in the same normal form as the WP expression
(e.g. `W64 (go.arrayLiteralSize [..])` from a spec's postcondition). -/
meta def simpIrisHyps (ivars : List IVarId) : TacticM Unit := withMainContext do
  for ivar in ivars do
    let mvar ← getMainGoal
    let gty ← instantiateMVars (← mvar.getType)
    let some g := parseIrisGoal? gty | return
    let some (_, _, _, P) := (hypsList g.hyps).find? (·.2.1 == ivar) | continue
    let P ← instantiateMVars P
    unless ← needsGooseSimp P do continue
    let (P', some pf) ← gooseExprSimp P | continue
    if P' == P then continue
    let motive ← withLocalDeclD `x (← inferType P) fun x => do
      let ⟨e', hyps'⟩ := changeHypType (bi := g.bi) ivar x g.hyps
      mkLambdaFVars #[x] (IrisGoal.toExpr { g with e := e', hyps := hyps' })
    let ⟨e'', hyps''⟩ := changeHypType (bi := g.bi) ivar P' g.hyps
    let newTy := IrisGoal.toExpr { g with e := e'', hyps := hyps'' }
    let newG ← mkFreshExprSyntheticOpaqueMVar newTy (← mvar.getTag)
    -- `gty = motive P` (definitionally), `motive P = motive P' = newTy`
    let heq ← mkCongrArg motive pf
    mvar.assign (← mkExpectedTypeHint (← mkEqMPR heq newG) gty)
    replaceMainGoal [newG.mvarId!]

/-- Run `tac` (an introduction), then simplify the hypotheses it introduced
(`simpIrisHyps`). -/
elab "wp_intro_simp " tac:tactic : tactic => do
  unless goose.wp.introSimp.get (← getOptions) do return ← evalTactic tac
  let before ← withMainContext do
    match parseIrisGoal? (← instantiateMVars (← getMainTarget)) with
    | some g => pure ((hypsList g.hyps).map (·.2.1))
    | none => pure []
  evalTactic tac
  let gs ← getGoals
  match gs with
  | [] => return
  | g :: _ =>
    let some ig := parseIrisGoal? (← instantiateMVars (← g.getType)) | return
    let new := (hypsList ig.hyps).map (·.2.1) |>.filter (!before.contains ·)
    unless new.isEmpty do
      let saved ← saveState
      try simpIrisHyps new catch _ => saved.restore

end focus

/-- `wp_apply lem $$ spats as pats`:
`wp_apply_core lem $$ spats`, then solve `isPkgInit` premises (`iPkgInit`),
introduce `pats` in the continuation, and run `wp_auto` on it. `with` is
accepted for `as`.

Options (written right after `wp_apply`; `--no-auto`/`--lc n` cannot be
used since `--` starts a Lean comment, and are rejected with an error):
* `wp_apply +noauto lem ... as pats`: introduce `pats` but do not run
  `wp_auto`, so the goal is `WP K[v] {{ Φ }}` right after the call (e.g. to
  `imod` a fancy update returned by the spec; to eliminate an update in the
  postcondition of the spec itself, first `iapply wp_fupd`).
* `wp_apply (lc := n) lem ... as pats`: the `wp_auto` after the call produces
  `n` later credits `Hlc1 ... Hlcn`; fails if there are fewer than `n` pure
  steps.

The continuation is the goal whose conclusion is the WP of the rest of the
program (tagged by `wp_apply_raw`), even when side goals come after it; if the
applied spec closes the goal, `as`/`wp_auto` are skipped. If the spec does not
apply, `wp_pures` is run first and it is tried again (e.g. for a call whose
argument is still `Pair (Val _) (Val _)`). To apply an Iris hypothesis `IH` with
Lean arguments, pass them as pure spec patterns: `wp_apply IH $$ %x %y [H]`.
The spec patterns are
iris-lean's, except that `[H] as name` (naming a premise goal) is not
available, so that `wp_apply lem $$ [H] as pats` introduces `pats`. -/
declare_syntax_cat wpApplyOpt
syntax (name := wpOptNoAuto) atomic("+" noWs &"noauto") : wpApplyOpt
syntax (name := wpOptLc) atomic(" (" &"lc" " := ") num ")" : wpApplyOpt
syntax wpAs := (" as " <|> " with ") (colGt ppSpace introPat)+

syntax (name := wpApply) "wp_apply" (ppSpace wpApplyOpt)* ppSpace wpPmTerm (wpAs)? : tactic

open Lean Elab Tactic in
/-- Reject the options `--no-auto`/`--lc n` after a `wp_apply`: they
are Lean comments, so they would be silently ignored. -/
meta def checkNoDashDashOpts (stx : Syntax) : TacticM Unit := do
  let some tail := stx.getTailPos? | return
  let src := (← getFileMap).source
  let rest := String.Pos.Raw.extract src tail src.rawEndPos
  let rest := ((rest.splitOn "\n").headD "").trimAsciiStart.toString
  if ["--no-auto", "--lc", "--auto"].any (fun (p : String) => rest.startsWith p) then
    throwErrorAt stx "wp_apply: `--no-auto`/`--lc n` are Lean comments here and would be \
      ignored; write `wp_apply +noauto lem ...` or `wp_apply (lc := n) lem ...`"

open Lean Elab Tactic Meta Iris.ProofMode in
/-- Internal (`wp_apply`): try to close the pure (Lean) side goals of the applied
spec that contain no metavariables, e.g. a constant bounds check `0 ≤ 0`, with
`decide` or `word`. Goals that are not propositions, or still contain
metavariables, are left alone. -/
elab "wp_apply_side" : tactic => do
  let gs ← getGoals
  let mut out := []
  for g in gs do
    if ← g.isAssigned then continue
    let ty ← instantiateMVars (← g.getType)
    if (isIrisGoal ty).or (ty.hasExprMVar.or !(← g.withContext (isProp ty))) then
      out := out ++ [g]; continue
    -- only closed (in)equations of numbers/words: `decide`, else `word`
    -- (both can be slow on other goals)
    let isArith (t : Lean.Expr) : Bool :=
      (t.isAppOfArity ``LE.le 4).or ((t.isAppOfArity ``LT.lt 4).or
        ((t.isAppOfArity ``Eq 3).and (((t.getArg! 0).isConstOf ``Int).or ((t.getArg! 0).isConstOf ``Nat))))
    let t ← whnfR ty
    let parts := if t.isAppOfArity ``And 2 then #[t.getArg! 0, t.getArg! 1] else #[t]
    unless parts.all isArith do
      out := out ++ [g]; continue
    setGoals [g]
    let saved ← saveState
    try
      evalTactic (← `(tactic| first | decide | word))
      unless (← getGoals).isEmpty do throwError "unsolved"
    catch _ =>
      saved.restore
      out := out ++ [g]
  setGoals out

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| wp_apply%$tk $opts:wpApplyOpt* $wpmt:wpPmTerm $[$as?:wpAs]?) => do
    checkNoDashDashOpts (← getRef)
    let _ := tk
    let mut noAuto := false
    let mut lc : Nat := 0
    for o in opts do
      if o.raw.isOfKind ``wpOptNoAuto then noAuto := true
      else if o.raw.isOfKind ``wpOptLc then
        lc := (o.raw.getArgs.findSome? (·.isNatLit?)).getD 0
      else throwErrorAt o "wp_apply: unknown option"
    let pmt ← liftMacroM <| wpPmTermToPmTerm wpmt
    let intro : TSyntax `tactic ←
      match as? with
      | some a =>
        let pats : TSyntaxArray `introPat := a.raw[1].getArgs.map (⟨·⟩)
        `(tactic| wp_focus_cont (wp_intro_simp (iintro $pats*)))
      | none => `(tactic| skip)
    let n := Syntax.mkNumLit (toString lc)
    let auto : TSyntax `tactic ←
      if noAuto then `(tactic| skip)
      else if lc == 0 then `(tactic| wp_focus_cont (try wp_auto_lc 0))
      -- credits were asked for: failing to produce them is an error
      else `(tactic| wp_focus_cont (wp_auto_lc $n))
    let core ← `(tactic| focus ((first | wp_apply_raw $pmt | (wp_pures; wp_apply_raw $pmt) | (wp_func_lits; wp_apply_raw $pmt) | (wp_pures; wp_apply_raw $pmt)) <;> wp_apply_post))
    evalTactic (← `(tactic| focus (($core:tactic) <;> (try iPkgInit); wp_apply_side; $intro:tactic; $auto:tactic; wp_untag_cont)))

section if_angelic_tac
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- `wp_if_angelic`: for an `if: #(decide P) then e else AngelicExit #()` at the
head of the WP expression, continue with `e` under the hypothesis `Hif : P`
(the `else` branch is trivial). Constant cost (unlike `wp_if_destruct`, which
simplifies the whole goal in both branches). -/
elab "wp_if_angelic" : tactic => do
  runTacticGooseWp `wp_if_angelic fun mvar g wp => do
    let some ((P, e1), K, _) ← findAngelicIf wp.e
      | throwIPMError "wp_if_angelic: no `if: #(decide P) then _ else AngelicExit #()` at the head"
    let Q := wp.mk' (← fillExpr K e1) wp.Φ
    let pP ← mkAppOptM ``BIBase.pure #[some g.prop, none, some P]
    let goal' ← mkAppOptM ``BIBase.wand #[some g.prop, none, some pP, some Q]
    let h ← addBIGoal g.hyps goal'
    mvar.assign (← wp.mkAppNamed ``tac_wp_if_angelic
      [("P", P), ("K", wp.quoteK K), ("e", e1), ("Δ", g.e), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ),
       ("!h", h)])

end if_angelic_tac

/-! ## Boolean cleanup -/

section bool_lemmas
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
  [go.PreSemantics]

theorem true_neq_false : (#true : val) ≠ #false := fun h =>
  absurd (go.intoVal_inj h) (by decide)
theorem false_neq_true : (#false : val) ≠ #true := fun h =>
  absurd (go.intoVal_inj h) (by decide)

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

/-- Simplify `if`s on `decide` conditions and `decide` of `True`/`False`. -/
macro "cleanup_bool_decide" : tactic => `(tactic|
  try simp only [if_decide_bool_eq_true, if_decide_bool_eq_false, if_decide_eq,
    if_decide_true_eq_false, if_decide_false_eq_true, decide_true, decide_false,
    Bool.false_eq_true, ↓reduceIte, ite_true, ite_false])

/-! ## Conditionals -/

section if_destruct
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Find a `decide p` (or `#b` for a Boolean variable `b`) in the WP expression. -/
meta def findIfCond (e : Lean.Expr) : MetaM (Option (Sum Lean.Expr Lean.Expr)) := do
  let e ← instantiateMVars e
  if let some d := e.find? (fun s => s.isAppOfArity ``Decidable.decide 2 && !s.hasLooseBVars) then
    return some (.inl (d.getArg! 0))
  if let some b := e.find? (fun s =>
      s.isAppOfArity ``GoGlobalContext.intoVal 4 && (s.getArg! 2).isConstOf ``Bool &&
        (s.getArg! 3).isFVar) then
    return some (.inr (b.getArg! 3))
  return none

/-- `#(decide P) = #b` (for a literal `b`) becomes `P`; other propositions are
unchanged. -/
meta def peelDecideEq (p : Lean.Expr) : MetaM Lean.Expr := do
  let p ← instantiateMVars p
  let_expr Eq _ a b := p | return p
  let a := a.consumeMData
  let b ← whnfR b
  unless a.isAppOfArity ``GoGlobalContext.intoVal 4 && b.isAppOfArity ``GoGlobalContext.intoVal 4 do
    return p
  let x := (a.getArg! 3).consumeMData
  let lit := (← whnfR (b.getArg! 3))
  unless lit.isConstOf ``Bool.true || lit.isConstOf ``Bool.false do return p
  if x.isAppOfArity ``Decidable.decide 2 then return x.getArg! 0
  return p

/-- The condition of the `if:` at the head of the WP expression: the `If c _ _`
in evaluation position whose condition `c` is a value (the next redex), or else
the outermost `If` in evaluation position. -/
meta def findHeadIf (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let mut outer : Option Lean.Expr := none
  for (_, e') in ← allEctx e do
    let e' ← whnfR (← instantiateMVars e')
    let_expr Perennial.Expr.If _ c _ _ := e' | continue
    if (← isGooseVal? c).isSome then return some c
    if outer.isNone then outer := some c
  return outer

end if_destruct

open Lean Elab Tactic Meta in
/-- Internal (`wp_if_destruct`): if `h : x = e` (or `e = x`) for a local
variable `x` and a term `e` that is not a variable (e.g. `W64 0` or `y + 1`),
substitute `x`. Equations between two variables (e.g. `i = n`, where it is not
clear which one should go) and other propositions are kept as `h`. -/
elab "wp_if_subst_closed " h:ident : tactic => withMainContext do
  let some d := (← getLCtx).findFromUserName? h.getId | return
  let ty ← instantiateMVars d.type
  let some (_, a, b) := ty.eq? | return
  let ok (x c : Lean.Expr) := x.isFVar && !c.isFVar && !c.containsFVar x.fvarId! && !c.hasMVar
  if ok a b || ok b a then
    liftMetaTactic fun g => do
      let some r ← observing? (Lean.Meta.subst g d.fvarId) | return [g]
      return [r]

set_option hygiene false in
open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_if_destruct`: case split on the condition of the `if:` at the head
of the WP expression — the first `decide P` (or Boolean variable `#b`) in it
(if there is no such `if:`, the first one in the expression, then in the whole
goal) — then `wp_pures`, `cleanup_bool_decide` and `wp_auto`. The case
hypothesis is `Hif` (accessible: the tactic is unhygienic).

Unlike earlier versions, a `decide` elsewhere in the expression (e.g. in a loop
postcondition) is not picked when there is an `if:` at the head. -/
elab "wp_if_destruct" : tactic => withMainContext do
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
    let post ← `(tactic| (wp_if_subst_closed Hif; wp_pures; cleanup_bool_decide; (try wp_auto); cleanup_bool_decide))
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

/-! ## Struct instances

`solve_into_val_typed_struct` proves `IntoValTypedUnderlying V T` for a struct type
`T = go.StructType fds` with the generic lemma `struct_into_val_typed`, whose
proofs of the allocation, load and store of a struct go field by field, by
induction over a list of field descriptions (`StructFieldDesc`); for a particular
struct only these descriptions (built from the field list and the
`StructFieldGet`/`StructFieldSet` step instances) and a few definitional facts are
checked. If this fails, the struct code is executed symbolically (`wp_auto`). -/

section struct_generic
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- A field of a struct with Lean type `V` and Go type `T`. -/
structure StructFieldDesc (V : Type) (T : go.GoType) where
  name : GoString
  ty : go.GoType
  F : Type
  [zv : ZeroVal F]
  [tpt : TypedPointsto (GF := GF) F]
  [ivt : IntoValTyped (GF := GF) F ty]
  proj : V → F
  upd : V → F → V
  get : ∀ x : V, go.IsGoStepPureDetTagged under (StructFieldGet T name) #x (Val #(proj x))
  set : ∀ (x : V) (y : F),
    go.IsGoStepPureDetTagged under (StructFieldSet T name) (PairV #x #y) (Val #(upd x y))

def fieldDeclName : go.field_decl → GoString
  | .FieldDecl n _ => n
  | .EmbeddedField n _ => n

def fieldDeclType : go.field_decl → go.GoType
  | .FieldDecl _ t => t
  | .EmbeddedField _ t => t

def FieldsMatch {V : Type} {T : go.GoType} :
    List go.field_decl → List (StructFieldDesc (GF := GF) V T) → Prop
  | [], [] => True
  | fd :: fds, f :: fs => fieldDeclName fd = f.name ∧ fieldDeclType fd = f.ty ∧ FieldsMatch fds fs
  | _, _ => False

def structFieldsPointsto {V : Type} {T : go.GoType} :
    List (StructFieldDesc (GF := GF) V T) → Loc → V → DFrac → IProp GF
  | [], _, _, _ => iprop(True)
  | f :: fs, l, v, dq =>
    iprop(@typedPointsto GF f.F f.tpt (structFieldRef V f.name l) (f.proj v) dq ∗
      structFieldsPointsto fs l v dq)

/-- The expansion of `GoAlloc (go.StructType fds) v` (`go.alloc_struct`). -/
def allocStructRaw (fds : List go.field_decl) (v : val) (fds_unsealed : List go.field_decl) : Expr :=
  gl(let: "l" := GoPrealloc #() in
       List.foldr (fun fd alloc_rest =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name "l")
                gl(let: "l_field" :=
                    GoAlloc field_type (StructFieldGet (go.StructType fds) field_name v) in
                  (if: ("l_field" =⟨go.PointerType field_type⟩ field_addr) then #()
                   else AngelicExit #()) ;;
                  alloc_rest)
         ) (#() : Expr) fds_unsealed ;;
       "l")


/-- One field of the expansion of `GoAlloc (go.StructType fds) v`, with the location
of the struct given by `l`. -/
def allocFieldExpr (T : go.GoType) (v : val) (l : Expr) (fd : go.field_decl) (rest : Expr) : Expr :=
  gl(let: "l_field" := GoAlloc (fieldDeclType fd) (StructFieldGet T (fieldDeclName fd) v) in
    (if: ("l_field" =⟨go.PointerType (fieldDeclType fd)⟩ (StructFieldRef T (fieldDeclName fd) l))
      then #() else AngelicExit #()) ;;
    rest)

theorem allocStructRaw_eq (fds : List go.field_decl) (v : val) (fds_unsealed : List go.field_decl) :
    allocStructRaw fds v fds_unsealed =
      gl(let: "l" := GoPrealloc #() in
        List.foldr (allocFieldExpr (go.StructType fds) v (Var "l")) (#() : Expr) fds_unsealed ;; "l") := by
  have h : (fun fd alloc_rest =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name "l")
                gl(let: "l_field" :=
                    GoAlloc field_type (StructFieldGet (go.StructType fds) field_name v) in
                  (if: ("l_field" =⟨go.PointerType field_type⟩ field_addr) then #()
                   else AngelicExit #()) ;;
                  alloc_rest)) = allocFieldExpr (go.StructType fds) v (Var "l") := by
    funext fd rest; cases fd <;> rfl
  unfold allocStructRaw
  rw [h]

theorem subst_allocFields (T : go.GoType) (v : val) (l : Loc) (fds : List go.field_decl) :
    subst "l" #l (List.foldr (allocFieldExpr T v (Var "l")) (#() : Expr) fds) =
      List.foldr (allocFieldExpr T v (Val #l)) (#() : Expr) fds := by
  induction fds with
  | nil => rfl
  | cons fd fds ih =>
    simp [List.foldr_cons, allocFieldExpr, subst, ih]

theorem closed_allocFields (T : go.GoType) (v : val) (l : Loc) (fds : List go.field_decl) (x : String) (w : val) :
    subst x w (List.foldr (allocFieldExpr T v (Val #l)) (#() : Expr) fds) =
      List.foldr (allocFieldExpr T v (Val #l)) (#() : Expr) fds := by
  induction fds with
  | nil => rfl
  | cons fd fds ih =>
    simp only [List.foldr_cons, allocFieldExpr, subst]
    split <;> simp_all

theorem struct_alloc_fields {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x : V) (l : Loc) (s : Stuckness) (E : CoPset) :
    ∀ (fds : List go.field_decl) (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))),
    FieldsMatch fds fs → ∀ (K : List EctxItem) (Φ : val → IProp GF),
    (structFieldsPointsto fs l x (DFrac.own 1) -∗ WP (fill K (Val #())) @ s; E {{ Φ }}) ⊢
      WP (fill K (List.foldr (allocFieldExpr (go.StructType fdsT) #x (Val #l)) (Val #()) fds))
        @ s; E {{ Φ }} := by
  intro fds
  induction fds with
  | nil =>
    intro fs hm K Φ
    cases fs with
    | nil =>
      simp only [List.foldr_nil]
      iintro H
      iapply H
      simp only [structFieldsPointsto]
      ipureintro; trivial
    | cons => exact absurd hm id
  | cons fd fds ih =>
    intro fs hm K Φ
    cases fs with
    | nil => exact absurd hm id
    | cons f fs =>
      obtain ⟨hn, ht, hm'⟩ := hm
      simp only [List.foldr_cons, allocFieldExpr, hn, ht]
      iintro H
      have _zv := f.zv
      have _tpt := f.tpt
      have _ivt := f.ivt
      have _get := f.get
      wp_pure
      wp_apply +noauto (IntoValTyped.wp_alloc (V := f.F) (t := f.ty) (f.proj x)) as %lf Hlf
      wp_pures
      rw [closed_allocFields]
      wp_if_angelic
      iintro %Hlf_eq
      subst Hlf_eq
      wp_pures
      iapply (ih fs hm' K Φ)
      iintro Hrest
      iapply H
      simp only [structFieldsPointsto]
      iframe

theorem struct_alloc_fields' {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x : V) (l : Loc) (s : Stuckness) (E : CoPset)
    (fds : List go.field_decl) (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT)))
    (hm : FieldsMatch fds fs) (Φ : val → IProp GF) :
    (structFieldsPointsto fs l x (DFrac.own 1) -∗ WP (Val #()) @ s; E {{ Φ }}) ⊢
      WP (List.foldr (allocFieldExpr (go.StructType fdsT) #x (Val #l)) (Val #()) fds)
        @ s; E {{ Φ }} :=
  struct_alloc_fields x l s E fds fs hm [] Φ

theorem wp_pure_raw_step {φ : Prop} {e1 e2 : Expr} [Hwp : PureWp (hlc := hlc) (GF := GF) φ e1 e2] (hφ : φ)
    {s : Stuckness} {E : CoPset} {Φ : val → IProp GF} :
    iprop(▷ WP e2 @ s; E {{ Φ }}) ⊢ WP e1 @ s; E {{ Φ }} :=
  tac_wp_pure_wp (Hwp := Hwp) (K := []) hφ .rfl .rfl

theorem struct_wp_alloc {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (v : V) :
    {{ (True : IProp GF) }} (App (Val (GoInstruction (GoAlloc t))) (Val #v)) @ s; E
    {{ (l : Loc), RET #l; l ↦ v }} := by
  iintro %Φ _ HΦ
  have hpw : PureWp (hlc := hlc) (GF := GF) True (App (Val (GoInstruction (GoAlloc t))) (Val #v))
      (allocStructRaw fds #v fds_unsealed) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) trivial)
  inext
  rw [allocStructRaw_eq]
  wp_bind (GoPrealloc #())
  iapply wp_GoPrealloc
  · itrivial
  inext
  iintro %l %Hl
  wp_pures
  rw [subst_allocFields]
  wp_bind (List.foldr _ _ _)
  iapply (struct_alloc_fields' v l s E fds_unsealed fs hfs)
  iintro Hfs
  wp_pures
  iapply HΦ
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  isplitl [Hfs]
  · iapply (hdef l v _).2
    iexact Hfs
  · ipureintro; exact Hl

/-! ### Load -/

/-- The expansion of `GoLoad (go.StructType fds) l` (`go.load_struct`). -/
def loadStructRaw (fds : List go.field_decl) (l : val) (fds_unsealed : List go.field_decl) : Expr :=
  gl(List.foldl (fun struct_so_far fd =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                let field_val := gl(GoLoad field_type field_addr)
                gl(StructFieldSet (go.StructType fds) field_name (struct_so_far, field_val))
         ) (GoZeroVal (go.StructType fds) #()) fds_unsealed)


/-- One field of the expansion of `GoLoad (go.StructType fds) l`. -/
def loadFieldExpr (T : go.GoType) (l : val) (so_far : Expr) (fd : go.field_decl) : Expr :=
  gl(StructFieldSet T (fieldDeclName fd)
    (so_far, GoLoad (fieldDeclType fd) (StructFieldRef T (fieldDeclName fd) l)))

theorem loadStructRaw_eq (fds : List go.field_decl) (l : val) (fds_unsealed : List go.field_decl) :
    loadStructRaw fds l fds_unsealed =
      List.foldl (loadFieldExpr (go.StructType fds) l) gl(GoZeroVal (go.StructType fds) #())
        fds_unsealed := by
  have h : (fun struct_so_far fd =>
                let (field_name, field_type) := match fd with
                                                | go.FieldDecl n t => (n, t)
                                                | go.EmbeddedField n t => (n, t)
                let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                let field_val := gl(GoLoad field_type field_addr)
                gl(StructFieldSet (go.StructType fds) field_name (struct_so_far, field_val))) =
      loadFieldExpr (go.StructType fds) l := by
    funext so_far fd; cases fd <;> rfl
  unfold loadStructRaw
  rw [h]

/-- The struct value built by the field-by-field load: the fields of `fs` set in `acc`
to the ones of `x`. -/
def structRebuild {V : Type} {T : go.GoType} :
    List (StructFieldDesc (GF := GF) V T) → V → V → V
  | [], acc, _ => acc
  | f :: fs, acc, x => structRebuild fs (f.upd acc (f.proj x)) x

theorem struct_load_fields {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x : V) (l : Loc) (dq : DFrac) (s : Stuckness)
    (E : CoPset) :
    ∀ (fds : List go.field_decl) (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))),
    FieldsMatch fds fs → ∀ (e0 : Expr) (acc : V) (P : IProp GF),
    (∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(P ∗ (P -∗ WP (fill K (Val #acc)) @ s; E {{ Ψ }})) ⊢ WP (fill K e0) @ s; E {{ Ψ }}) →
    ∀ (K : List EctxItem) (Φ : val → IProp GF),
    iprop(P ∗ structFieldsPointsto fs l x dq ∗
      ((P ∗ structFieldsPointsto fs l x dq) -∗
        WP (fill K (Val #(structRebuild fs acc x))) @ s; E {{ Φ }})) ⊢
      WP (fill K (List.foldl (loadFieldExpr (go.StructType fdsT) #l) e0 fds)) @ s; E {{ Φ }} := by
  intro fds
  induction fds with
  | nil =>
    intro fs hm e0 acc P he0 K Φ
    cases fs with
    | nil =>
      simp only [List.foldl_nil, structRebuild, structFieldsPointsto]
      iintro ⟨HP, Ht, H⟩
      iapply (he0 K Φ)
      iframe HP
      iintro HP
      iapply H
      iframe
    | cons => exact absurd hm id
  | cons fd fds ih =>
    intro fs hm e0 acc P he0 K Φ
    cases fs with
    | nil => exact absurd hm id
    | cons f fs =>
      obtain ⟨hn, ht, hm'⟩ := hm
      simp only [List.foldl_cons, structRebuild, structFieldsPointsto]
      iintro ⟨HP, ⟨Hf, Hfs⟩, H⟩
      iapply (ih fs hm' (loadFieldExpr (go.StructType fdsT) #l e0 fd) (f.upd acc (f.proj x))
        iprop(P ∗ @typedPointsto GF f.F f.tpt (structFieldRef V f.name l) (f.proj x) dq) ?_ K Φ)
      · intro K' Ψ
        simp only [loadFieldExpr, hn, ht]
        iintro ⟨⟨HP, Hf⟩, H⟩
        have h2 : iprop(P ∗ (P -∗ WP (fill K' (App (Val (GoInstruction (StructFieldSet (go.StructType fdsT) f.name)))
              (Pair (Val #acc) (App (Val (GoInstruction (GoLoad f.ty)))
                (App (Val (GoInstruction (StructFieldRef (go.StructType fdsT) f.name))) (Val #l))))))
              @ s; E {{ Ψ }})) ⊢
            WP (fill K' (App (Val (GoInstruction (StructFieldSet (go.StructType fdsT) f.name)))
              (Pair e0 (App (Val (GoInstruction (GoLoad f.ty)))
                (App (Val (GoInstruction (StructFieldRef (go.StructType fdsT) f.name))) (Val #l))))))
              @ s; E {{ Ψ }} :=
          he0 (EctxItem.PairLCtx (App (Val (GoInstruction (GoLoad f.ty)))
              (App (Val (GoInstruction (StructFieldRef (go.StructType fdsT) f.name))) (Val #l))) ::
            EctxItem.AppRCtx (Val (GoInstruction (StructFieldSet (go.StructType fdsT) f.name))) :: K') Ψ
        iapply h2
        iframe HP
        iintro HP
        have _zv := f.zv
        have _tpt := f.tpt
        have _ivt := f.ivt
        have _set := f.set
        wp_pures
        wp_apply +noauto (IntoValTyped.wp_load (V := f.F) (t := f.ty) _ dq (f.proj x)) $$ Hf as Hf
        wp_pures
        iapply H
        iframe
      · iframe HP Hf Hfs
        iintro ⟨⟨HP, Hf⟩, Hfs⟩
        iapply H
        iframe

theorem struct_load_fields' {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x : V) (l : Loc) (dq : DFrac) (s : Stuckness)
    (E : CoPset) (fds : List go.field_decl)
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))) (hm : FieldsMatch fds fs)
    (e0 : Expr) (acc : V) (P : IProp GF)
    (he0 : ∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(P ∗ (P -∗ WP (fill K (Val #acc)) @ s; E {{ Ψ }})) ⊢ WP (fill K e0) @ s; E {{ Ψ }})
    (Φ : val → IProp GF) :
    iprop(P ∗ structFieldsPointsto fs l x dq ∗
      ((P ∗ structFieldsPointsto fs l x dq) -∗
        WP (Val #(structRebuild fs acc x)) @ s; E {{ Φ }})) ⊢
      WP (List.foldl (loadFieldExpr (go.StructType fdsT) #l) e0 fds) @ s; E {{ Φ }} :=
  struct_load_fields x l dq s E fds fs hm e0 acc P he0 [] Φ

theorem struct_wp_load {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    (hrebuild : ∀ x, structRebuild fs (zero_val V) x = x)
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (l : Loc) (dq : DFrac)
    (v : V) :
    {{ (l ↦{dq} v : IProp GF) }} (App (Val (GoInstruction (GoLoad t))) (Val #l)) @ s; E
    {{ RET #v; l ↦{dq} v }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  icases Hl with ⟨Hl, %Hnn⟩
  ihave Hl := (hdef l v dq).1 $$ Hl
  have hpw : PureWp (hlc := hlc) (GF := GF) True (App (Val (GoInstruction (GoLoad t))) (Val #l))
      (loadStructRaw fds #l fds_unsealed) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) trivial)
  inext
  rw [loadStructRaw_eq]
  have he0 : ∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(emp ∗ (emp -∗ WP (fill K (Val #(zero_val V))) @ s; E {{ Ψ }})) ⊢
        WP (fill K gl(GoZeroVal (go.StructType fds) #())) @ s; E {{ Ψ }} := by
    intro K Ψ
    iintro ⟨-, H⟩
    wp_pure
    iapply H
    itrivial
  iapply (struct_load_fields' v l dq s E fds_unsealed fs hfs _ (zero_val V) emp he0 Φ)
  iframe Hl
  iintro ⟨-, Hl⟩
  rw [hrebuild]
  wp_pures
  iapply HΦ
  isplitl [Hl]
  · iapply (hdef l v dq).2
    iexact Hl
  · ipureintro; exact Hnn

/-! ### Store -/

/-- The expansion of `GoStore (go.StructType fds) (l, v)` (`go.store_struct`). -/
def storeStructRaw (fds : List go.field_decl) (l v : val) (fds_unsealed : List go.field_decl) :
    Expr :=
  gl(List.foldl (fun store_so_far fd =>
                gl(store_so_far ;;
                  (let (field_name, field_type) := match fd with
                                                  | go.FieldDecl n t => (n, t)
                                                  | go.EmbeddedField n t => (n, t)
                   let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                   let field_val := gl(StructFieldGet (go.StructType fds) field_name v)
                   gl(GoStore field_type (field_addr, field_val))))
         ) (#() : Expr) fds_unsealed)


/-- One field of the expansion of `GoStore (go.StructType fds) (l, v)`. -/
def storeFieldExpr (T : go.GoType) (l v : val) (so_far : Expr) (fd : go.field_decl) : Expr :=
  gl(so_far ;; GoStore (fieldDeclType fd)
    (StructFieldRef T (fieldDeclName fd) l, StructFieldGet T (fieldDeclName fd) v))

theorem storeStructRaw_eq (fds : List go.field_decl) (l v : val)
    (fds_unsealed : List go.field_decl) :
    storeStructRaw fds l v fds_unsealed =
      List.foldl (storeFieldExpr (go.StructType fds) l v) (Val #()) fds_unsealed := by
  have h : (fun store_so_far fd =>
                gl(store_so_far ;;
                  (let (field_name, field_type) := match fd with
                                                  | go.FieldDecl n t => (n, t)
                                                  | go.EmbeddedField n t => (n, t)
                   let field_addr := gl(StructFieldRef (go.StructType fds) field_name l)
                   let field_val := gl(StructFieldGet (go.StructType fds) field_name v)
                   gl(GoStore field_type (field_addr, field_val))))) =
      storeFieldExpr (go.StructType fds) l v := by
    funext so_far fd; cases fd <;> rfl
  unfold storeStructRaw
  rw [h]

theorem struct_store_fields {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x y : V) (l : Loc) (s : Stuckness)
    (E : CoPset) :
    ∀ (fds : List go.field_decl) (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))),
    FieldsMatch fds fs → ∀ (e0 : Expr) (Pin Pout : IProp GF),
    (∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(Pin ∗ (Pout -∗ WP (fill K (Val #())) @ s; E {{ Ψ }})) ⊢ WP (fill K e0) @ s; E {{ Ψ }}) →
    ∀ (K : List EctxItem) (Φ : val → IProp GF),
    iprop(Pin ∗ structFieldsPointsto fs l x (DFrac.own 1) ∗
      ((Pout ∗ structFieldsPointsto fs l y (DFrac.own 1)) -∗
        WP (fill K (Val #())) @ s; E {{ Φ }})) ⊢
      WP (fill K (List.foldl (storeFieldExpr (go.StructType fdsT) #l #y) e0 fds)) @ s; E {{ Φ }} := by
  intro fds
  induction fds with
  | nil =>
    intro fs hm e0 Pin Pout he0 K Φ
    cases fs with
    | nil =>
      simp only [List.foldl_nil, structFieldsPointsto]
      iintro ⟨HP, Ht, H⟩
      iapply (he0 K Φ)
      iframe HP
      iintro HP
      iapply H
      iframe
    | cons => exact absurd hm id
  | cons fd fds ih =>
    intro fs hm e0 Pin Pout he0 K Φ
    cases fs with
    | nil => exact absurd hm id
    | cons f fs =>
      obtain ⟨hn, ht, hm'⟩ := hm
      simp only [List.foldl_cons, structFieldsPointsto]
      iintro ⟨HP, ⟨Hf, Hfs⟩, H⟩
      iapply (ih fs hm' (storeFieldExpr (go.StructType fdsT) #l #y e0 fd)
        iprop(Pin ∗ @typedPointsto GF f.F f.tpt (structFieldRef V f.name l) (f.proj x) (DFrac.own 1))
        iprop(Pout ∗ @typedPointsto GF f.F f.tpt (structFieldRef V f.name l) (f.proj y) (DFrac.own 1))
        ?_ K Φ)
      · intro K' Ψ
        simp only [storeFieldExpr, hn, ht]
        iintro ⟨⟨HP, Hf⟩, H⟩
        have h2 : iprop(Pin ∗ (Pout -∗ WP (fill K' gl(#() ;; GoStore f.ty
              (StructFieldRef (go.StructType fdsT) f.name #l,
                StructFieldGet (go.StructType fdsT) f.name #y))) @ s; E {{ Ψ }})) ⊢
            WP (fill K' gl(e0 ;; GoStore f.ty
              (StructFieldRef (go.StructType fdsT) f.name #l,
                StructFieldGet (go.StructType fdsT) f.name #y))) @ s; E {{ Ψ }} :=
          he0 (EctxItem.AppRCtx (Rec BAnon BAnon gl(GoStore f.ty
              (StructFieldRef (go.StructType fdsT) f.name #l,
                StructFieldGet (go.StructType fdsT) f.name #y))) :: K') Ψ
        iapply h2
        iframe HP
        iintro HP
        have _zv := f.zv
        have _tpt := f.tpt
        have _ivt := f.ivt
        have _get := f.get
        wp_pures
        wp_apply +noauto (wp_store (V := f.F) (t := f.ty) _ (f.proj x) (f.proj y)) $$ Hf as Hf
        iapply H
        iframe
      · iframe HP Hf Hfs
        iintro ⟨⟨HP, Hf⟩, Hfs⟩
        iapply H
        iframe

theorem struct_store_fields_nil {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x y : V) (l : Loc) (s : Stuckness)
    (E : CoPset) (fds : List go.field_decl)
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))) (hm : FieldsMatch fds fs)
    (e0 : Expr) (Pin Pout : IProp GF)
    (he0 : ∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(Pin ∗ (Pout -∗ WP (fill K (Val #())) @ s; E {{ Ψ }})) ⊢ WP (fill K e0) @ s; E {{ Ψ }})
    (Φ : val → IProp GF) :
    iprop(Pin ∗ structFieldsPointsto fs l x (DFrac.own 1) ∗
      ((Pout ∗ structFieldsPointsto fs l y (DFrac.own 1)) -∗ WP (Val #()) @ s; E {{ Φ }})) ⊢
      WP (List.foldl (storeFieldExpr (go.StructType fdsT) #l #y) e0 fds) @ s; E {{ Φ }} :=
  struct_store_fields x y l s E fds fs hm e0 Pin Pout he0 [] Φ

theorem struct_store_fields' {V : Type} {fdsT : List go.field_decl} [ZeroVal V]
    [go.TypeReprUnderlying (go.StructType fdsT) V] (x y : V) (l : Loc) (s : Stuckness)
    (E : CoPset) (fds : List go.field_decl)
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fdsT))) (hm : FieldsMatch fds fs)
    (Φ : val → IProp GF) :
    iprop(structFieldsPointsto fs l x (DFrac.own 1) ∗
      (structFieldsPointsto fs l y (DFrac.own 1) -∗ WP (Val #()) @ s; E {{ Φ }})) ⊢
      WP (List.foldl (storeFieldExpr (go.StructType fdsT) #l #y) (Val #()) fds) @ s; E {{ Φ }} := by
  have he0 : ∀ (K : List EctxItem) (Ψ : val → IProp GF),
      iprop(emp ∗ (emp -∗ WP (fill K (Val #())) @ s; E {{ Ψ }})) ⊢
        WP (fill K (Val #())) @ s; E {{ Ψ }} := by
    intro K Ψ
    iintro ⟨-, H⟩
    iapply H
    itrivial
  iintro ⟨Hx, H⟩
  iapply (struct_store_fields_nil x y l s E fds fs hm (Val #()) emp emp he0 Φ)
  iframe Hx
  iintro ⟨-, Hy⟩
  iapply H
  iexact Hy

theorem struct_wp_store {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    {s : Stuckness} {E : CoPset} {t : go.GoType} [t ↓u go.StructType fds] (l : Loc) (v w : V) :
    {{ (l ↦ v : IProp GF) }} (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w))) @ s; E
    {{ RET #(); l ↦ w }} := by
  iintro %Φ Hl HΦ
  rw [typedPointsto_unseal]
  unfold typedPointstoWrap
  icases Hl with ⟨Hl, %Hnn⟩
  ihave Hl := (hdef l v _).1 $$ Hl
  have hpw : PureWp (hlc := hlc) (GF := GF) True
      (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w)))
      (storeStructRaw fds #l #w fds_unsealed) := by
    have _tagged := @go.tagged_internal_inst
    infer_instance
  iapply (wp_pure_raw_step (Hwp := hpw) trivial)
  inext
  rw [storeStructRaw_eq]
  iapply (struct_store_fields' v w l s E fds_unsealed fs hfs Φ)
  iframe Hl
  iintro Hl
  wp_pures
  iapply HΦ
  isplitl [Hl]
  · iapply (hdef l w _).2
    iexact Hl
  · ipureintro; exact Hnn

/-! ### The instance -/

theorem struct_into_val_typed {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    {fds fds_unsealed : List go.field_decl} [EqualsUnfold fds fds_unsealed]
    [hrepr : go.TypeReprUnderlying (go.StructType fds) V]
    (fs : List (StructFieldDesc (GF := GF) V (go.StructType fds)))
    (hfs : FieldsMatch fds_unsealed fs)
    (hdef : ∀ l v dq, typedPointstoDef l v dq ⊣⊢ structFieldsPointsto fs l v dq)
    (hrebuild : ∀ x, structRebuild fs (zero_val V) x = x) :
    IntoValTypedUnderlying (GF := GF) V (go.StructType fds) where
  wp_alloc_def v := struct_wp_alloc fs hfs hdef v
  wp_load_def l dq v := struct_wp_load fs hfs hdef hrebuild l dq v
  wp_store_def l v w := struct_wp_store fs hfs hdef l v w
  type_repr_def := hrepr

end struct_generic

section struct_tac
open Lean Elab Tactic Meta

/-- A literal list. -/
meta partial def structListLit? (e : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let e ← whnfR e
  if e.isAppOfArity ``List.nil 1 then return some []
  unless e.isAppOfArity ``List.cons 3 do return none
  let some t ← structListLit? (e.getArg! 2) | return none
  return some (e.getArg! 1 :: t)

/-- Prove `IntoValTypedUnderlying V T` for a struct type `T = go.StructType fds` from
the generic lemma `struct_into_val_typed`: the field descriptions are built from
the field list, their projections and updates are determined by the
`StructFieldGet`/`StructFieldSet` step instances. -/
elab "solve_into_val_typed_struct_gen" : tactic => withMainContext do
  evalTactic (← `(tactic| refine struct_into_val_typed ?fs ?hfs ?hdef ?hrebuild))
  let [gfs, ghfs, ghdef, ghreb] ← getGoals
    | throwError "solve_into_val_typed_struct_gen: unexpected goals"
  -- the field list `fds_unsealed`, from `FieldsMatch fds_unsealed ?fs`
  let hfsTy ← instantiateMVars (← ghfs.getType)
  let fdsU := hfsTy.getAppArgs[hfsTy.getAppNumArgs - 2]!
  let some fds ← structListLit? fdsU | throwError "solve_into_val_typed_struct_gen: fields {fdsU}"
  let fsTy ← whnfR (← instantiateMVars (← gfs.getType))
  let descTy := fsTy.appArg!
  let V := descTy.getAppArgs[descTy.getAppNumArgs - 2]!
  let T := descTy.getAppArgs[descTy.getAppNumArgs - 1]!
  gfs.withContext do
    let mut elems := #[]
    for fd in fds do
      let fd ← whnfR fd
      let n := fd.getAppArgs[fd.getAppNumArgs - 2]!
      let ty := fd.getAppArgs[fd.getAppNumArgs - 1]!
      elems := elems.push (← `(StructFieldDesc.mk (V := $(← Term.exprToSyntax V))
        (T := $(← Term.exprToSyntax T)) $(← Term.exprToSyntax n) $(← Term.exprToSyntax ty) _ _ _
        (fun _ => inferInstance) (fun _ _ => inferInstance)))
    let fsStx ← `([$elems,*])
    setGoals [gfs]
    evalTactic (← `(tactic| exact $fsStx))
  setGoals [ghfs]
  evalTactic (← `(tactic| simp only [FieldsMatch, fieldDeclName, fieldDeclType, and_self]))
  setGoals [ghdef]
  evalTactic (← `(tactic| (intro _ _ _; exact .rfl)))
  setGoals [ghreb]
  evalTactic (← `(tactic| (intro x; cases x; rfl)))

end struct_tac


section frame_exact
open Lean Elab Tactic Meta Qq Iris.ProofMode

theorem tac_frame_exact_hyp {PROP : Type _} [BI PROP] {Δ Δ' A Q : PROP}
    (h : Δ ⊣⊢ Δ' ∗ A) (h' : Δ' ⊢ Q) : Δ ⊢ A ∗ Q :=
  h.1.trans (sep_comm.1.trans (sep_mono_right h'))

theorem tac_frame_exact_assoc {PROP : Type _} [BI PROP] {Δ A B Q : PROP}
    (h : Δ ⊢ A ∗ (B ∗ Q)) : Δ ⊢ (A ∗ B) ∗ Q := h.trans sep_assoc.2

theorem tac_frame_exact_true_l {PROP : Type _} [BI PROP] {Δ Q : PROP}
    (h : Δ ⊢ Q) : Δ ⊢ True ∗ Q := h.trans true_sep_mpr

theorem tac_frame_exact_true {PROP : Type _} [BI PROP] {Δ : PROP} : Δ ⊢ True := true_intro

/-- Is `P` the proposition `True`? -/
meta def isTrueProp (P : Lean.Expr) : Bool :=
  let P := P.consumeMData
  P.isAppOfArity ``BIBase.pure 3 && (P.getArg! 2).consumeMData.isConstOf ``True

/-- Frame, along the `∗`-spine of the goal, the conjuncts that are equal to spatial
hypotheses (`avail`; syntactically, or else definitionally for a hypothesis with
the same head, tried in order), and `True`; stops at the first conjunct that is
neither, leaving the rest as a new goal. Typically linear in the size of the goal
(`iframe` searches a `Frame` instance per hypothesis and conjunct). -/
meta partial def frameExactCore {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Q($prop)) (avail : List (IVarId × Lean.Expr)) :
    ProofModeM Lean.Expr := do
  let goal ← instantiateMVars goal
  let g := goal.consumeMData
  if isTrueProp g then
    return ← mkAppNamed ``tac_frame_exact_true [("PROP", prop), ("Δ", ehyps)]
  unless g.isAppOfArity ``BIBase.sep 4 do return ← addBIGoal hyps goal
  let A := (g.getArg! 2).consumeMData
  let Q := g.getArg! 3
  if A.isAppOfArity ``BIBase.sep 4 then
    let goal' := mkApp4 g.getAppFn (g.getArg! 0) (g.getArg! 1) (A.getArg! 2)
      (mkApp4 g.getAppFn (g.getArg! 0) (g.getArg! 1) (A.getArg! 3) Q)
    let pf ← frameExactCore hyps goal' avail
    return ← mkAppNamed ``tac_frame_exact_assoc
      [("PROP", prop), ("Δ", ehyps), ("A", A.getArg! 2), ("B", A.getArg! 3), ("Q", Q), ("!h", pf)]
  if isTrueProp A then
    let pf ← frameExactCore hyps Q avail
    return ← mkAppNamed ``tac_frame_exact_true_l
      [("PROP", prop), ("Δ", ehyps), ("Q", Q), ("!h", pf)]
  -- a hypothesis equal to `A`, or else (in order) one with the same head that is
  -- definitionally equal (e.g. up to instances or the form of a projection)
  let found ← match avail.find? (·.2 == A) with
    | some (ivar, _) => pure (some ivar)
    | none => avail.findSomeM? fun (ivar, ty) => do
      unless ty.getAppFn == A.getAppFn && ty.getAppNumArgs == A.getAppNumArgs do return none
      if A.hasMVar || ty.hasMVar then return none
      let ok ← tryCatchRuntimeEx (Core.withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := 20000 * 1000 }) <|
        withNewMCtxDepth <| withTransparency .default <| isDefEq ty A) fun _ => pure false
      return if ok then some ivar else none
  let some ivar := found | return ← addBIGoal hyps goal
  let r := hyps.remove false ivar
  let pf ← frameExactCore r.hyps' Q (avail.filter (·.1 != ivar))
  mkAppNamed ``tac_frame_exact_hyp
    [("PROP", prop), ("Δ", ehyps), ("Δ'", r.e'), ("A", r.out), ("Q", Q), ("h", r.pf), ("!h'", pf)]

/-- Internal (`solve_into_val_typed_struct`): frame the conjuncts of the goal that
are equal to spatial hypotheses, in one pass along the goal (see
`frameExactCore`); the remaining goal is left to `iframe`. -/
elab "iframe_exact" : tactic => do
  ProofModeM.runTactic `iframe_exact fun mvar g => do
    let mut avail := []
    for (_, ivar, p, ty) in (hypsList g.hyps).reverse do
      unless isTrue p do avail := (ivar, (← instantiateMVars ty).consumeMData) :: avail
    mvar.assign (← frameExactCore g.hyps g.goal avail)

end frame_exact

/-- Internal (`solve_into_val_typed_struct`): prove `IntoValTypedUnderlying V T`
by executing the struct code symbolically. -/
macro "solve_into_val_typed_struct_steps" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typedPointsto_unseal, typedPointstoWrap]
  · intro s E t _ v
    iintro %Φ _ HΦ
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    wp_apply wp_GoPrealloc as %l %Hnotnull
    try wp_auto_angelic
    subst_vars
    iapply HΦ
    try simp only [TypedPointsto.typedPointstoDef, named]
    (try iframe_exact); (try iframe)
    ipureintro; (try simp only [and_self]); exact Hnotnull
  · intro s E t _ l dq v
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    try simp only [TypedPointsto.typedPointstoDef]
    iNamed Hl
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    try wp_auto
    cases v
    try simp only
    iapply HΦ
    try simp only [TypedPointsto.typedPointstoDef, named]
    (try iframe_exact); (try iframe)
    ipureintro; (try simp only [and_self]); exact Hnn
  · intro s E t _ l v w
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    try simp only [TypedPointsto.typedPointstoDef]
    iNamed Hl
    have _tagged := @go.tagged_internal_inst
    wp_pure
    clear _tagged
    try wp_auto
    cases w
    iapply HΦ
    try simp only [TypedPointsto.typedPointstoDef, named]
    (try iframe_exact); (try iframe)
    ipureintro; (try simp only [and_self]); exact Hnn
  · infer_instance))

/-- `solve_into_val_typed_struct`: prove `IntoValTypedUnderlying V T` for
a struct type `T` whose typed points-to is the conjunction of its (named)
field points-tos: with the generic lemma `struct_into_val_typed`
(`solve_into_val_typed_struct_gen`), or else by symbolic execution. -/
macro "solve_into_val_typed_struct" : tactic =>
  `(tactic| first
    | (solve_into_val_typed_struct_gen; done)
    | solve_into_val_typed_struct_steps)

instance equals_unfold_nil (A : Type) : EqualsUnfold (@List.nil A) (@List.nil A) := ⟨rfl⟩

section intoVal_typed_unit
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

instance intoVal_typed_unit : IntoValTypedUnderlying (GF := GF) Unit (go.StructType []) := by
  solve_into_val_typed_struct

end intoVal_typed_unit

/-! ## Loops -/

/-- `wp_for`: apply `wp_for` to the loop at the head of the goal with the
current context as invariant (see `wp_for_core`), then clean up. `wp_for H`
additionally destructs `H` with `iNamed`. -/
syntax "wp_for" (ppSpace colGt ident)? : tactic

macro_rules
  | `(tactic| wp_for) => `(tactic| (wp_for_core; (try wp_auto); cleanup_bool_decide; (try wp_auto)))
  | `(tactic| wp_for $h:ident) =>
    `(tactic| (wp_for_core; iNamed $h:ident; (try wp_auto); cleanup_bool_decide; (try wp_auto)))

/-- `wp_for_post`: prove a `forPostcondition` goal (see
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
/-- `wp_end`: finish a function proof by applying the continuation `HΦ`
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
