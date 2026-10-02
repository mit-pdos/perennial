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
  introduced with `%x` (Rocq `as (x) "..."`).
* Rocq's global `wp_apply_auto_default` switch is not ported; use `--no-auto`.
* `wp_if_destruct` names the case hypothesis `Hif` (Rocq leaves it anonymous)
  and substitutes it when it is an equation with a variable side.
-/
import Perennial.Golang.Theory.Pkg

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## Function and method calls -/

/-- Rocq `wp_func_call`: rewrite `#(functions f ts)` with its `FuncUnfold`
instance and try to solve `is_pkg_init` goals. -/
macro "wp_func_call" : tactic => `(tactic| (rw [func_unfold]; (try iPkgInit)))

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
progress was made. -/
partial def iWpAuto {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (lc : Nat) (lcIdx : Nat := 1)
    (simpFirst : Bool := true) :
    ProofModeM (Expr × Nat × Bool) := do
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
  if let some ⟨_, hyps', e', k⟩ ← observing? (iWpPureStep hyps wp (failOnUnsolved := true)
      (lc := lc > 0)) then
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
  if let some ⟨_, hyps', e', k⟩ ← observing? (iWpLoadStep hyps wp) then
    let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx
    return (← k pf', lc', true)
  -- store
  if let some ⟨_, hyps', e', k⟩ ← observing? (iWpStoreStep hyps wp) then
    let (pf', lc', _) ← iWpAuto hyps' { wp with e := e' } lc lcIdx
    return (← k pf', lc', true)
  -- allocation of a local variable
  let res ← IO.mkRef lc
  if let some pf ← observing? (iWpAllocStep hyps wp (auto := true) none fun hyps' wp' => do
      let (pf', lc', _) ← iWpAuto hyps' wp' lc lcIdx
      res.set lc'
      return pf') then
    return (pf, ← res.get, true)
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

/-- `wp_apply lem $$ spats as pats` (Rocq `wp_apply (lem with "spats") as "pats"`):
`wp_apply_core lem $$ spats`, then solve `is_pkg_init` premises (`iPkgInit`),
introduce `pats` in the continuation (the last goal), and run `wp_auto` on it
(`--no-auto` disables this; `--lc n` makes `wp_auto` produce `n` credits).
`with` is accepted for `as`. -/
syntax wpNoAuto := " --no-auto"
syntax wpLc := " --lc " num
syntax wpAs := (" as " <|> " with ") (colGt ppSpace introPat)+

syntax (name := wpApply) "wp_apply " pmTerm (wpNoAuto)? (wpLc)? (wpAs)? : tactic

macro_rules
  | `(tactic| wp_apply $pmt:pmTerm $[$na:wpNoAuto]? $[$lc:wpLc]? $[$as?:wpAs]?) => do
    let intro : Lean.TSyntax `tactic ←
      match as? with
      | some a =>
        let pats : Lean.TSyntaxArray `introPat := a.raw[1].getArgs.map (⟨·⟩)
        `(tactic| focusLastIrisGoal (iintro $pats*))
      | none => `(tactic| skip)
    let n : Lean.TSyntax `num := match lc with
      | some l => ⟨l.raw[1]⟩
      | none => Lean.Syntax.mkNumLit "0"
    let auto : Lean.TSyntax `tactic ←
      if na.isSome then `(tactic| skip)
      else `(tactic| focusLastIrisGoal (try wp_auto_lc $n))
    `(tactic| focus ((wp_apply_core $pmt) <;> (try iPkgInit); $intro:tactic; $auto:tactic))

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

end if_destruct

set_option hygiene false in
open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Rocq `wp_if_destruct`: case split on the first `decide P` (or Boolean
variable `#b`) in the WP expression, then `wp_pures`, `cleanup_bool_decide` and
`wp_auto`. The case hypothesis is `Hif` (accessible: the tactic is unhygienic). -/
elab "wp_if_destruct" : tactic => do
  let some g := parseIrisGoal? (← instantiateMVars (← getMainTarget))
    | throwError "wp_if_destruct: not in the Iris proof mode"
  let target ← match ← parseGooseWp? g.goal with
    | some wp => Pure.pure wp.e
    | none => Pure.pure g.goal
  let cond ← match ← findIfCond target with
    | some c => Pure.pure (some c)
    | none => findIfCond g.goal
  match cond with
  | some (.inl p) =>
    let pStx ← Term.exprToSyntax p
    evalTactic (← `(tactic| by_cases Hif : $pStx))
    evalTactic (← `(tactic| all_goals (
      (first | simp only [decide_eq_true Hif, ↓reduceIte] |
        simp only [decide_eq_false Hif, Bool.false_eq_true, ↓reduceIte] | skip);
      (try subst Hif);
      wp_pures;
      cleanup_bool_decide;
      (try wp_auto);
      cleanup_bool_decide)))
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

set_option hygiene false in
/-- Rocq `wp_end`: finish a function proof by applying the continuation `HΦ`
(or `HPost`) and trying to discharge the remaining goal. -/
macro "wp_end" : tactic => `(tactic| (
  wp_pures
  repeat imodintro
  (first
  | iapply HΦ
  | iapply HPost);
  (try (first
    | (iframe; done)
    | itrivial
    | (ipureintro; trivial)
    | (iframe; ipureintro; trivial)))))

end Perennial
