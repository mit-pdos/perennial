/-
Named propositions, and related proof mode helpers.

`name ∷ P` is equivalent to `P` but knows to name itself `name` when
destructed by `iNamed`. Write definitions with `"H" ∷ P` for each conjunct,
then use `iNamed H` to destruct a hypothesis `H` into its conjuncts using their
specified names; `iNamed` also introduces the existentials at the top with the
names of their binders.

The name of a named proposition is an iris-lean **cases pattern**, written as a
string: `"H"`, `"#H"` (move to the intuitionistic context), `"%H"` (move to the
Lean context), or any other `icasesPat` such as `"⟨H1, H2⟩"`. The special name
`"*"` means "destruct this conjunct recursively with `iNamed`".

Tactics:
* `iNamed H` — destruct `H` (existentials, then the separating-conjunction
  spine of named conjuncts), naming the conjuncts. Definitions at the head of
  `H`'s type are unfolded (unless `@[irreducible]`). An unnamed conjunct stops the destruction; the rest keeps the name
  `H`.
* `iNamed 1` — introduce the premise of a wand/implication and `iNamed` it.
* `iNamedPrefix H "pre"` / `iNamedSuffix H "suf"` — like `iNamed`, adding a
  prefix/suffix to the introduced identifiers.
* `iNamedDestruct H` — `iNamed` without destructing existentials.
* `iNamedAccu` — solve a goal that is a metavariable with the separating
  conjunction of the spatial hypotheses, each named with its current name.
* `iFrameNamed` — frame each named conjunct of the goal with the hypothesis of
  the same name.
* `iExactEq H` — prove the goal `Q` from `H : P`, leaving `P = Q` as a goal.
-/
module

public import Iris.ProofMode

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

/-- `named name P` (notation `name ∷ P`) is `P`, but `iNamed` names it `name`
when destructing. It is reducible, so typeclass search sees through it. -/
@[reducible] def named {A : Type _} (_name : String) (P : A) : A := P

/-- `name ∷ P` is `named name P`. It binds more tightly than `∗` (so
`"H1" ∷ P ∗ "H2" ∷ Q` names both conjuncts). -/
syntax:36 term:max " ∷ " term:36 : term

macro_rules
  | `(iprop($n ∷ $P)) => `(named $n iprop($P))
  | `($n ∷ $P) => `(named $n iprop($P))

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab named]
meta def delabNamed : Delab := do
  let e ← getExpr
  guard <| e.getAppNumArgs == 3
  let n ← withNaryArg 1 delab
  let P ← withNaryArg 2 delab
  let P ← BI.unpackIprop P
  `(iprop($n ∷ $P))

section
variable {PROP : Type _} [BI PROP]

theorem to_named (name : String) (P : PROP) : P ⊢ named name P := .rfl
theorem from_named (name : String) (P : PROP) : named name P ⊢ P := .rfl

theorem tac_delay_split (R P Q : PROP) : (P ∗ R) ⊢ (R -∗ Q) -∗ P ∗ Q := by
  iintro ⟨HP, HR⟩ Hwand
  isplitl [HP]
  · iexact HP
  · iapply Hwand $$ HR

theorem tac_exact_eq {Δ P Q : PROP} (h1 : Δ ⊢ P) (h : P = Q) : Δ ⊢ Q := h ▸ h1
end

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Replace the type of hypothesis `ivar` by a definitionally equal one. -/
meta def changeHypType {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (ivar : IVarId)
    (newTy : Q($prop)) : ∀ {e}, Hyps bi e → (e' : Q($prop)) × Hyps bi e'
  | _, .emp h => ⟨_, .emp h⟩
  | _, h@(.hyp _ name ivar' p _ _) =>
    if ivar == ivar' then ⟨_, Hyps.mkHyp bi name ivar p newTy⟩ else ⟨_, h⟩
  | _, .sep _ _ _ _ lhs rhs =>
    let ⟨_, l⟩ := changeHypType ivar newTy lhs
    let ⟨_, r⟩ := changeHypType ivar newTy rhs
    ⟨_, Hyps.mkSep l r⟩

/-- Is `e` (syntactically) `named n P`? Returns `(n, P)`. -/
meta def isNamed? (e : Lean.Expr) : Option (String × Lean.Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``named 3 then
    match e.getArg! 1 with
    | .lit (.strVal s) => some (s, e.getArg! 2)
    | _ => none
  else none

meta def isBIExists (e : Lean.Expr) : Bool := e.consumeMData.isAppOfArity ``BIBase.exists 4
meta def isBISep (e : Lean.Expr) : Bool := e.consumeMData.isAppOfArity ``BIBase.sep 4

/-- `▷ Q` as `(▷ ·, Q)`. -/
meta def isLater? (e : Lean.Expr) : Option (Lean.Expr × Lean.Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``BIBase.later 3 then some (e.appFn!, e.appArg!) else none

/-- Unfold definitions at the head of `e` until it is a `named`, `∃` or `∗`
(or nothing can be unfolded). Irreducible definitions are not unfolded. -/
meta partial def unfoldNamedHead (e : Lean.Expr) (fuel : Nat := 64) : MetaM Lean.Expr := do
  if fuel == 0 then return e
  let e ← instantiateMVars e
  if (isNamed? e).isSome || isBIExists e || isBISep e then return e
  let e' ← whnfR e
  if (isNamed? e').isSome || isBIExists e' || isBISep e' then return e'
  match e'.getAppFn with
  | .const c _ =>
    if (← getReducibilityStatus c) matches .irreducible then return e'
    -- never unfold BI connectives or other class projections
    if (← isProjectionFn c) then return e'
    -- nor `if`/`match` (unfolding `ite` exposes a raw `Decidable.rec` on the
    -- instance, which may be classical and send the kernel into a deep
    -- recursion): case split or `simp` first
    if [``ite, ``dite, ``cond, ``Decidable.rec, ``Decidable.casesOn].contains c then return e'
    if Lean.Meta.isMatcherCore (← getEnv) c then return e'
    match ← unfoldDefinition? e' with
    | some e'' => unfoldNamedHead e''.headBeta (fuel - 1)
    | none => return e'
  | _ => return e'

/-- How to name a single named conjunct. -/
inductive NamedPat where
  /-- an iris-lean cases pattern (as a string) -/
  | pat (s : String)
  /-- `"*"`: destruct recursively; the conjunct is first introduced under the
  given (fresh) name -/
  | star (tmp : Name)

/-- Parse the name `n` of a named proposition into a cases pattern, applying
`f` to the identifier it introduces (for prefixes/suffixes). -/
meta def parseNamedPat (n : String) (f : String → String) : TacticM NamedPat := do
  if n == "*" then
    let i ← mkFreshId
    return .star (Name.mkSimple ("__Hstar_" ++ (i.toString.map fun c => if c.isAlphanum then c else '_')))
  let n' :=
    if n.startsWith "#" then "#" ++ f (n.drop 1).toString
    else if n.startsWith "%" then "%" ++ f (n.drop 1).toString
    else if n.all (fun c => c.isAlphanum || c == '_' || c == '\'') then f n
    else n
  match Parser.runParserCategory (← getEnv) `icasesPat n' with
  | .ok _ => return .pat n'
  | .error err => throwError "iNamed: cannot parse the name {repr n} as a cases pattern: {err}"

/-- The hypothesis introduced by a simple cases pattern `H` or `#H`. -/
meta def patIdent (p : String) : String :=
  if p.startsWith "#" || p.startsWith "∗" then (p.drop 1).toString else p

/-- Parse a cases pattern. -/
meta def parsePat (s : String) : TacticM (TSyntax `icasesPat) := do
  match Parser.runParserCategory (← getEnv) `icasesPat s with
  | .ok stx => return ⟨stx⟩
  | .error err => throwError "cannot parse the cases pattern {repr s}: {err}"

/-- Look up an Iris hypothesis by name in the main goal. -/
meta def findIrisHyp (h : Name) : TacticM (IrisGoal × IVarId × Lean.Expr) := do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType))
    | throwError "not in the Iris proof mode"
  let some (ivar, ty) := g.hyps.find? h | throwError "hypothesis {h} not found"
  return (g, ivar, ty)

/-- Hypotheses `H : "H" ∷ P` (whose name is the one they carry). -/
meta def collectNamedHyps {u} {prop : Q(Type u)} {bi : Q(BI $prop)} (names : List String) :
    ∀ {e}, Hyps bi e → List (IVarId × Lean.Expr)
  | _, .emp _ => []
  | _, .hyp _ name ivar _ ty _ =>
    match isNamed? ty with
    | some (_, P) => if names.contains name.toString then [(ivar, P)] else []
    | none =>
      -- `▷ (n ∷ P)` (from destructing a hypothesis under a later)
      match isLater? ty with
      | some (lf, Q) => match isNamed? Q with
        | some (_, P) => if names.contains name.toString then [(ivar, mkApp lf P)] else []
        | none => []
      | none => []
  | _, .sep _ _ _ _ lhs rhs => collectNamedHyps names lhs ++ collectNamedHyps names rhs

/-- Strip the `named` wrapper from every hypothesis `H : "H" ∷ P`. -/
meta def stripNamedHyps (names : List String) : TacticM Unit := do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return
  let hs := collectNamedHyps names g.hyps
  if hs.isEmpty then return
  let mut st : (e : Q($(g.prop))) × Hyps g.bi e := ⟨g.e, g.hyps⟩
  for (ivar, P) in hs do
    st := changeHypType (bi := g.bi) ivar P st.2
  (← getMainGoal).setType (IrisGoal.toExpr { g with e := st.1, hyps := st.2 })

/-- Unfold the head of hypothesis `h`'s type (see `unfoldNamedHead`). -/
meta def unfoldHypHead (h : Name) : TacticM Lean.Expr := do
  let (g, ivar, ty) ← findIrisHyp h
  -- under a later `▷ Q`: unfold `Q`
  let ty' ← match isLater? ty with
    | some (lf, Q) => do
      let Q' ← unfoldNamedHead Q
      pure (if Q' == Q then ty else mkApp lf Q')
    | none => unfoldNamedHead ty
  if ty' != ty then
    let ⟨e', hyps'⟩ := changeHypType (bi := g.bi) ivar ty' g.hyps
    let mvar ← getMainGoal
    mvar.setType (IrisGoal.toExpr { g with e := e', hyps := hyps' })
  return ty'

/-- The binder name of an existential `∃ x, P` (as a usable identifier). -/
meta def existsBinderName (e : Lean.Expr) : MetaM Name := do
  let e := e.consumeMData
  let body := e.getArg! 3
  match body with
  | .lam n _ _ _ =>
    let n := n.eraseMacroScopes
    if n.isAnonymous || n.isInternal then return `x else return n
  | _ => return `x

mutual
/-- Core of `iNamed`: name the conjuncts of `h`. `deex`: destruct top-level
existentials first. -/
meta partial def iNamedCore (h : Name) (f : String → String) (deex : Bool) : TacticM Unit :=
  -- the goal (and with it the local context) changes after each `icases`, which
  -- may introduce new Lean variables (`%x`): all inspection of hypothesis types
  -- must happen in the main goal's context
  withMainContext do
  let ty0 ← unfoldHypHead h
  -- a hypothesis `▷ Q` is destructed according to `Q` (`icases` distributes the
  -- later); if that fails (e.g. an `∃` of a type that is not `Inhabited`), it is
  -- left alone
  let underLater := (isLater? ty0).isSome
  let ty := match isLater? ty0 with | some (_, Q) => Q | none => ty0
  if underLater then
    unless (isNamed? ty).isSome || isBIExists ty || isBISep ty do return
    let saved ← saveState
    try iNamedCore' h f deex ty catch _ => saved.restore
    return
  iNamedCore' h f deex ty

/-- `iNamedCore` on the hypothesis `h` whose (unfolded, possibly under a later)
type is `ty`. -/
meta partial def iNamedCore' (h : Name) (f : String → String) (deex : Bool) (ty : Lean.Expr) : TacticM Unit :=
  withMainContext do
  -- a single named hypothesis
  if let some (n, _) := isNamed? ty then
    nameOne h n f
    return
  -- existentials
  if deex && isBIExists ty then
    let x ← existsBinderName ty
    let pat ← parsePat s!"⟨%{x.toString}, {h.toString}⟩"
    evalTactic (← `(tactic| icases $(mkIdent h):ident with $pat))
    iNamedCore h f deex
    return
  -- separating conjunction spine: collect named conjuncts
  if isBISep ty then
    let mut pats : Array String := #[]
    let mut stars : Array Name := #[]
    let mut cur := ty
    let mut restNamed := false
    repeat
      let cur' ← if (isNamed? cur).isSome then pure cur else whnfR cur
      unless isBISep cur' do
        if let some (n, _) := isNamed? cur' then
          match ← parseNamedPat n f with
          | .pat p => pats := pats.push p
          | .star tmp =>
            pats := pats.push tmp.toString
            stars := stars.push tmp
          restNamed := true
        break
      let lhs := cur'.getArg! 2
      let rhs := cur'.getArg! 3
      let some (n, _) := isNamed? lhs | break
      match ← parseNamedPat n f with
      | .pat p => pats := pats.push p
      | .star tmp =>
        pats := pats.push tmp.toString
        stars := stars.push tmp
      cur := rhs
    if pats.isEmpty then return
    unless restNamed do
      -- the unnamed rest keeps the name `h`, unless a conjunct is called `h`
      if (pats.map patIdent).contains h.toString then
        pats := pats.push (← mkFreshUserName `Hrest).eraseMacroScopes.toString
      else pats := pats.push h.toString
    let pat ← parsePat ("⟨" ++ ", ".intercalate pats.toList ++ "⟩")
    evalTactic (← `(tactic| icases $(mkIdent h):ident with $pat))
    stripNamedHyps (pats.toList.map patIdent)
    for s in stars do iNamedCore s f true
    return
  -- anything else: leave the hypothesis alone

/-- Name the hypothesis `h : n ∷ P` according to the pattern `n`. -/
meta partial def nameOne (h : Name) (n : String) (f : String → String) : TacticM Unit := do
  match ← parseNamedPat n f with
  | .star _ =>
    -- strip the name and recurse
    let (g, ivar, ty) ← findIrisHyp h
    let some (_, P) := isNamed? ty | return
    let ⟨e', hyps'⟩ := changeHypType (bi := g.bi) ivar P g.hyps
    (← getMainGoal).setType (IrisGoal.toExpr { g with e := e', hyps := hyps' })
    iNamedCore h f true
  | .pat p =>
    evalTactic (← `(tactic| icases $(mkIdent h):ident with $(← parsePat p)))
    stripNamedHyps [patIdent p]
end

/-- `iNamed` (see the module docstring). -/
syntax (name := iNamedTac) "iNamed" (ppSpace colGt (ident <|> num))? : tactic
/-- `iNamedPrefix H "pre"`: `iNamed H`, prefixing the introduced names with `pre`. -/
syntax "iNamedPrefix " ident ppSpace str : tactic
/-- `iNamedSuffix H "suf"`: `iNamed H`, suffixing the introduced names with `suf`. -/
syntax "iNamedSuffix " ident ppSpace str : tactic
/-- `iNamedDestruct H`: `iNamed` without destructing existentials. -/
syntax "iNamedDestruct " ident : tactic

/-- Name all anonymous-but-named hypotheses: hypotheses whose type is `n ∷ P`. -/
meta partial def iNamedAll : TacticM Unit := do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return
  let some (h, _, _, _) ← g.hyps.findM? (m := TacticM) fun _ _ _ ty => pure (isNamed? ty).isSome
    | return
  iNamedCore h id true
  -- avoid looping if the hypothesis is still named
  let some g' := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return
  if let some (_, ty) := g'.hyps.find? h then
    if (isNamed? ty).isSome then return
  iNamedAll

elab_rules : tactic
  | `(tactic| iNamed $h:ident) => iNamedCore h.getId id true
  | `(tactic| iNamed $_n:num) => do
    let h ← mkFreshUserName `Hnamed
    evalTactic (← `(tactic| iintro $(mkIdent h):ident))
    iNamedCore h id true
  | `(tactic| iNamed) => iNamedAll
  | `(tactic| iNamedPrefix $h:ident $p:str) => iNamedCore h.getId (p.getString ++ ·) true
  | `(tactic| iNamedSuffix $h:ident $p:str) => iNamedCore h.getId (· ++ p.getString) true
  | `(tactic| iNamedDestruct $h:ident) => iNamedCore h.getId id false

/-- The separating conjunction of the spatial hypotheses, each wrapped in
`named` with its current name (mirroring `Hyps.buildAccuProof`). -/
meta partial def namedAccuProp {u} {prop : Q(Type u)} {bi : Q(BI $prop)} :
    ∀ {e}, Hyps bi e → Q($prop) → MetaM Q($prop)
  | _, .emp _, acc => return acc
  | _, .hyp _ name _ p ty _, acc => do
    if isTrue p then return acc
    let n := if name.isAnonymous || name.hasMacroScopes then "?" else name.toString
    let nty : Q($prop) := mkApp3 (mkConst ``named [u]) prop (mkStrLit n) ty
    if acc == q(iprop(emp)) then return nty
    else return q(iprop($nty ∗ $acc))
  | _, .sep _ _ _ _ lhs rhs, acc => do
    let acc ← namedAccuProp rhs acc
    namedAccuProp lhs acc

/-- `iNamedAccu`: solve a goal that is a metavariable `?P` with the
separating conjunction of all spatial hypotheses, each named by its current
name (so that `iNamed` restores the context). -/
elab "iNamedAccu" : tactic => do
  ProofModeM.runTactic `iNamedAccu fun mvar { prop, hyps, goal, .. } => do
    let goal ← instantiateMVars goal
    unless goal.isMVar do throwIPMError "{goal} is not a metavariable"
    let ⟨_, pf⟩ := hyps.buildAccuProof
    let namedP ← namedAccuProp (prop := prop) hyps q(iprop(emp))
    unless ← isDefEq goal namedP do
      throwIPMError "could not assign goal metavariable to {namedP}"
    mvar.assign pf

/-- `iFrameNamed`: frame each conjunct `"H" ∷ P` of the goal with the
hypothesis `H`. -/
elab "iFrameNamed" : tactic => withMainContext do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType))
    | throwError "not in the Iris proof mode"
  let mut names : Array Name := #[]
  let goal ← instantiateMVars g.goal
  let collect (e : Lean.Expr) : StateT (Array Name) MetaM Unit := do
    e.forEach' fun s => do
      if let some (n, _) := isNamed? s then
        let n := if n.startsWith "#" || n.startsWith "%" then (n.drop 1).toString else n
        if n.all (fun c => c.isAlphanum || c == '_' || c == '\'') then
          modify (·.push (Name.mkSimple n))
      return true
  let ((), ns) ← (collect goal).run #[]
  names := ns
  for n in names do
    evalTactic (← `(tactic| try iframe $(mkIdent n):ident))

/-- `iExactEq H`: prove the goal `Q` from the hypothesis `H : P`, leaving
the Lean goal `P = Q`. -/
elab "iExactEq " h:ident : tactic => withMainContext do
  let (g, _, P) ← findIrisHyp h.getId
  let mvar ← getMainGoal
  let Q := g.goal
  let eqTy ← mkEq P Q
  let mEq ← mkFreshExprSyntheticOpaqueMVar eqTy
  let goalP := IrisGoal.toExpr { g with goal := P }
  let mP ← mkFreshExprSyntheticOpaqueMVar goalP
  mvar.assign (← mkAppM ``tac_exact_eq #[mP, mEq])
  setGoals [mP.mvarId!]
  evalTactic (← `(tactic| iexact $h:ident))
  setGoals [mEq.mvarId!]

/-- `iSplitDelay`: split a `P ∗ Q` goal, proving `P` (first goal) with
an accumulated remainder `R` that is then available in the second goal as the
premise of a wand. -/
macro "iSplitDelay" : tactic =>
  `(tactic| iapply tac_delay_split _ _ _ $$ [-] [])

end tactics

end Perennial
