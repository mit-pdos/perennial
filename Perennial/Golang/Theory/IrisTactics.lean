/-
Perennial-side extensions and fixes of iris-lean proof mode tactics (no Rocq
counterpart file; Rocq gets these from Iris/stdpp).

* `solve_ndisj` (Rocq/stdpp `solve_ndisj`): prove mask side conditions about
  namespaces, e.g. `↑(N.@"inv") ⊆ ⊤ ∖ ↑(N.@"sema")`, `⊤ ∖ ↑N ⊆ ⊤ ∖ ↑(N.@"x")` or
  `↑(N.@"a") ## ↑(N.@"b")`, using hypotheses about masks from the context.
  It is hooked into `trivial`, so iris-lean's side-condition solver (used by
  `iinv`, `imod`, `iapply` of fancy updates, `TCSideCondition` instances, ...)
  discharges these goals automatically.
* `iinv` is re-implemented (same syntax and behaviour as iris-lean's) with a
  side-condition solver that never runs `simp [*]` (which could hit the maximum
  recursion depth with word facts in the context, or on the `Atomic` condition
  of a large WP goal) and that solves namespace conditions with `solve_ndisj`.
  An unsolved condition is left as a goal (as in iris-lean); an `Atomic`
  condition on a non-atomic expression is an error suggesting `wp_bind`.
-/
import Iris.ProofMode

namespace Perennial

open Iris Iris.BI Iris.Std

/-! ## `solve_ndisj` -/

section ndisj

theorem ndisj_mem_ndot {A : Type _} [Pos.Countable A] {N : Namespace} {x : A} {p : Pos}
    (h : p ∈ (↑(N.@x) : CoPset)) : p ∈ (↑N : CoPset) := nclose_subseteq N x p h

theorem ndisj_ndot_eq {A : Type _} [Pos.Countable A] {N : Namespace} {x y : A} {p : Pos}
    (h1 : p ∈ (↑(N.@x) : CoPset)) (h2 : p ∈ (↑(N.@y) : CoPset)) : x = y :=
  Classical.byContradiction fun hne => ndot_ne_disjoint N hne p ⟨h1, h2⟩

theorem ndisj_mem_top {p : Pos} : p ∈ (⊤ : CoPset) := CoPset.mem_full

theorem ndisj_subset_iff {E1 E2 : CoPset} : E1 ⊆ E2 ↔ ∀ p, p ∈ E1 → p ∈ E2 := Iff.rfl

theorem ndisj_disj_iff {E1 E2 : CoPset} : E1 ## E2 ↔ ∀ p, ¬ (p ∈ E1 ∧ p ∈ E2) := Iff.rfl

theorem ndisj_ns_disj_iff {N1 N2 : Namespace} :
    N1 ## N2 ↔ ∀ p, ¬ (p ∈ (↑N1 : CoPset) ∧ p ∈ (↑N2 : CoPset)) := Iff.rfl

end ndisj

section ndisj_tac
open Lean Elab Tactic Meta

/-- Is `e` a mask side condition that `solve_ndisj` should try: a (conjunction
of) `E1 ⊆ E2`, `E1 ## E2` or `p ∈ E` over `CoPset`s, or `N1 ## N2` over
namespaces? -/
partial def isNdisjGoal (e : Expr) : MetaM Bool := do
  let e ← whnfR (← instantiateMVars e)
  if e.isAppOfArity ``And 2 then
    return (← isNdisjGoal (e.getArg! 0)) && (← isNdisjGoal (e.getArg! 1))
  if e.isAppOfArity ``True 0 then return true
  if e.isAppOfArity ``Not 1 then return ← isNdisjGoal (e.getArg! 0)
  if e.isAppOfArity ``HasSubset.Subset 4 || e.isAppOfArity ``Iris.Std.Disjoint.disjoint 4 then
    let ty := e.getArg! 0
    return ty.isConstOf ``CoPset || ty.isConstOf ``Namespace ||
      (← whnfR ty).isConstOf ``CoPset
  if e.isAppOfArity ``Membership.mem 5 then
    return (e.getArg! 1).isConstOf ``CoPset
  return false

/-- Does the type of a local hypothesis talk about masks or namespaces? -/
def isNdisjHyp (ty : Expr) : Bool :=
  (ty.find? fun s => s.isConstOf ``CoPset || s.isConstOf ``nclose || s.isConstOf ``ndot).isSome

/-- Rocq `solve_ndisj`: prove a mask side condition built from `⊆`, `##`, `∈`,
`∪`, `∩`, `∖`, `⊤`, `∅` and namespaces `↑N`, `↑(N.@x)` (with distinct `x`s for
disjointness), using the hypotheses about masks in the context. Fails on goals
of another shape. -/
elab "solve_ndisj" : tactic => withMainContext do
  let g ← getMainGoal
  unless ← isNdisjGoal (← g.getType) do
    throwError "solve_ndisj: not a mask (namespace) side condition"
  -- only keep the hypotheses about masks (the context may hold many unrelated
  -- facts, e.g. word arithmetic, that would slow down `grind`)
  let mut irrelevant := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then
      unless isNdisjHyp (← instantiateMVars d.type) do irrelevant := irrelevant.push d.fvarId
  let g ← g.tryClearMany irrelevant
  replaceMainGoal [g]
  evalTactic (← `(tactic| (
    try simp only [ndisj_subset_iff, ndisj_disj_iff, ndisj_ns_disj_iff] at *
    grind [→ ndisj_mem_ndot, → ndisj_ndot_eq, LawfulSet.mem_diff, LawfulSet.mem_union,
      LawfulSet.mem_inter, CoPset.mem_full, ndisj_mem_top, LawfulSet.mem_empty])))

end ndisj_tac

/-- iris-lean's side-condition solver tries `trivial`: let it solve mask side
conditions about namespaces (`solve_ndisj` fails immediately on other goals). -/
macro_rules | `(tactic| trivial) => `(tactic| solve_ndisj)

/-! ## `iinv` -/

namespace IrisTactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- `wandM`/`Option.getD` reduction (copy of iris-lean's private `reduceWandM`). -/
def reduceWandM (e : Expr) : ProofModeM Expr := do
  let simpThms ← #[``BIBase.wandM, ``Option.getD].foldlM (·.addDeclToUnfold ·) {}
  let simpContext ← Simp.mkContext {} #[simpThms] (← getSimpCongrTheorems)
  Lean.Meta.dsimp e simpContext <&> Prod.fst

/-- Try to close `goal` (a side condition of `iinv`) with `tac`, catching all
errors, including runtime ones (deep recursion, heartbeats). -/
def tryCloseWith (goal : MVarId) (tac : TSyntax `tactic) : TermElabM Bool := do
  let saved ← saveState
  let msgs ← Core.getMessageLog
  tryCatchRuntimeEx (do
    let gs ← Tactic.run goal (withoutRecover <| evalTactic tac)
    -- a goal admitted by error recovery (e.g. inside `all_goals`) is a failure
    if gs.isEmpty && !(← Core.getMessageLog).hasErrors then return true
    saved.restore; Core.setMessageLog msgs; return false)
    (fun _ => do saved.restore; Core.setMessageLog msgs; return false)

/-- Solve the side condition `φ` of `iinv` (a conjunction): mask conditions with
`solve_ndisj`, others with `trivial`/`infer_instance`/`simp`; unsolved parts
become new goals. An `Atomic` condition that cannot be proved is an error. -/
partial def solveInvSidecondition (φ : Q(Prop)) : ProofModeM Q($φ) := do
  let φ ← instantiateMVars φ
  if φ.isAppOfArity ``And 2 then
    let a : Q(Prop) := φ.getArg! 0
    let b : Q(Prop) := φ.getArg! 1
    let pa ← solveInvSidecondition a
    let pb ← solveInvSidecondition b
    return mkApp4 (mkConst ``And.intro) a b pa pb
  if φ.isConstOf ``True then return mkConst ``True.intro
  let pf ← mkFreshExprSyntheticOpaqueMVar φ
  let g := pf.mvarId!
  let solved ← liftM (m := TermElabM) do
    if ← isNdisjGoal φ then
      if ← tryCloseWith g (← `(tactic| solve_ndisj)) then return true
    for tac in [← `(tactic| trivial), ← `(tactic| infer_instance),
        ← `(tactic| (simp; done))] do
      if ← tryCloseWith g tac then return true
    return false
  unless solved do
    if φ.getAppFn.constName?.any (fun n => n matches .str _ "Atomic") then
      throwIPMError "the expression of the WP is not atomic: use `wp_bind` to focus \
        on the atomic operation first{indentExpr φ}"
    addMVarGoal g
  return pf

private def iInvCore {u} {prop : Q(Type u)} {bi} {e}
    (hyps : Hyps bi e) (goal : Q($prop)) (ivar : IVarId) (specPat : Option SpecPat)
    (casesPat : iCasesPat) (closePat : Option iCasesPat) :
    ProofModeM Q($e ⊢ $goal) := do
  let ⟨_, hyps', _, Pinv, _, _, pfEq⟩ := hyps.remove false ivar
  let φ ← mkFreshExprMVarQ q(Prop)
  let Pin : Q($prop) ← mkFreshExprMVarQ q($prop)
  let X : Q(Type) ← mkFreshExprMVarQ q(Type)
  let Pout ← mkFreshExprMVarQ q($X → $prop)
  let close := if closePat.isSome then q(true) else q(false)
  let mPclose ← mkFreshExprMVarQ q(Option ($X → $prop))
  let Q' ← mkFreshExprMVarQ q($X → $prop)
  let some inst ← ProofModeM.trySynthInstanceQ
    q(ElimInv $φ $X $Pinv $Pin $Pout $close $mPclose $goal $Q')
  | throwIPMError "invalid invariant {Pinv} (ElimInv type class synthesis failed)"
  let ⟨e'', hyps'', p'', out'', pfPin⟩ ←
    iSpecializeCoreNoModal hyps' q(false) q(iprop($Pin -∗ $Pin))
    [specPat.getD ⟨← getRef, .autoframe .spatial⟩]
  have : $out'' =Q $Pin := ⟨⟩
  have : $p'' =Q false := ⟨⟩
  let hφ ← solveInvSidecondition q($φ)
  let Pout' : Q($X → $prop) ← reduceWandM Pout
  let Q'' : Q($X → $prop) ← reduceWandM Q'
  match mPclose with
  | ~q(some $f) =>
    let f' : Q($X → $prop) ← reduceWandM f
    let pf : Q(∀ x, $e'' ∗ $Pout x ∗ $f x ⊢ $Q' x) ←
      withLocalDeclDQ (← mkFreshUserName .anonymous) X fun x => do
        match closePat with
        | some closePat =>
          let pf' ← iCasesCore hyps'' q($Q'' $x) ⟨closePat.ref, (.conjunction [casesPat, closePat])⟩
            q(false) q(iprop($Pout' $x ∗ $f' $x))
          mkLambdaFVars #[x] pf'
        | none => throwIPMError "missing cases pattern for the closing hypothesis"
    return q(tac_inv_elim $inst $hφ $pf $pfEq $pfPin)
  | ~q(none) =>
    let pf : Q(∀ x, $e'' ∗ $Pout x ⊢ $Q' x) ←
      withLocalDeclDQ (← mkFreshUserName .anonymous) X fun x => do
        let pf' ← iCasesCore hyps'' q($Q'' $x) casesPat q(false) q($Pout' $x)
        mkLambdaFVars #[x] pf'
    return q(tac_inv_elim $inst $hφ $pf $pfEq $pfPin)

/-- Perennial's `iinv` (shadows iris-lean's `iinv`, with the same syntax; see the
module docstring): side conditions are solved without `simp [*]`, mask conditions
by `solve_ndisj`.

`iinv H with casesPat closePat` opens the invariant hypothesis `H` (or, for a
namespace `N`, the invariant hypothesis with that namespace), destructs its
contents with `casesPat` and the closing update with `closePat`; `iinv H $$ spat
with ...` uses `spat` for the resources needed to open it. -/
syntax (name := perennialIinv) (priority := high) "iinv " colGt term (" $$ " colGt ppSpace specPat)?
    " with " colGt icasesPat (colGt icasesPat)? : tactic

elab_rules : tactic
  | `(tactic| iinv $t:term $[$$ $spat:specPat]?
      with $casesPat:icasesPat $[$closePat:icasesPat]?) => do
    let specPat ← liftMacroM <| spat.mapM SpecPat.parse
    let casesPat ← liftMacroM <| iCasesPat.parse casesPat
    let closePat ← liftMacroM <| closePat.mapM iCasesPat.parse
    ProofModeM.runTactic `iinv fun mvar { hyps, goal, .. } => do
      let ivar ← do match ← try? <| hyps.findWithInfo ⟨t⟩ with
      | some ivar => pure ivar
      | none =>
        let N ← elabTermEnsuringTypeQ t q(Namespace)
        let some (_, ivar, _, _) ← hyps.findM? fun _ _ _ ty =>
            return (← ProofModeM.trySynthInstanceQ q(IntoInv $ty $N)).isSome
          | throwIPMError "invariant hypothesis with the namespace {N} not found"
        pure ivar
      let pf ← iInvCore hyps goal ivar specPat casesPat closePat
      mvar.assign pf

end IrisTactics

end Perennial
