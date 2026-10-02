/-
Port of `new/golang/theory/proofmode.v`: the `PureWp` class and the core WP
tactics for GooseLang (`wp_pure`, `wp_pures`, `wp_pure_lc`, `wp_call`,
`wp_bind`, `wp_apply_core`, `wp_value`, `wp_finish`, `wp_expr_simp`).

The tactics are Lean elaborators over the iris-lean proof mode, modeled after
iris-lean's `Iris/HeapLang/ProofMode.lean`.

## Differences from Rocq

* `PureWp φ e e'` has `φ` and `e'` as `outParam`s, so ordinary typeclass
  search finds the next step of `e` (Rocq: `Hint Mode PureWp ... ! -`).
* The Rocq `Hint Extern` for `wp_call` (only fire on a syntactic `RecV`) is an
  ordinary instance: Lean's discrimination trees never unfold the head
  `Val (RecV ...)`, so a sealed definition hidden behind a constant is not
  called accidentally. `wp_call` additionally unfolds a constant head (as
  Rocq's `unify` does).
* After each step, the expression is simplified with the `goose_wp_simp` simp
  set: substitution (`subst`, `subst'`) is computed, `fill` is unfolded.
  This is the analogue of Rocq's `simpl subst'; simpl fill`.
* WP goals are any iris-lean `Wp.wp` over GooseLang's `expr` (the `IrisGS_gen`
  instance is `goose_irisGS`, built from `gooseGlobalGS`/`gooseLocalGS`, or from
  `heapGS`). Stuckness `s` plays the role of Rocq's `stk`.
-/
import Perennial.GooseLang.Lifting
import Perennial.Golang.Theory.SimpAttr
import Perennial.Golang.Theory.Display
import Perennial.Golang.Defn.Pre
import Iris.ProofMode

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## The `PureWp` class -/

section classes
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]

/-- Classes that are used to tell `wp_pures` about steps it can take:
`PureWp φ e e'` says that, under the pure side condition `φ`, `e` takes a
step (yielding a later credit) to `e'`, in any evaluation context. -/
class PureWp (φ : outParam Prop) (e : expr) (e' : outParam expr) : Prop where
  pure_wp_wp : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) (K : List ectx_item), φ →
    iprop(▷ (£ 1 -∗ WP (fill K e') @ s; E {{ Φ }})) ⊢ WP (fill K e) @ s; E {{ Φ }}

export PureWp (pure_wp_wp)

theorem tac_wp_pure_wp {φ : Prop} {e1 e2 : expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (h : Δ' ⊢ WP (fill K e2) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  hlater.trans <| (later_mono (wand_intro (sep_elim_left.trans h))).trans
    (Hwp.pure_wp_wp s E Φ K hφ)

theorem tac_wp_pure_wp_later_credit {φ : Prop} {e1 e2 : expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (h : Δ' ⊢ iprop(£ 1 -∗ WP (fill K e2) @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  hlater.trans <| (later_mono h).trans (Hwp.pure_wp_wp s E Φ K hφ)

/-- `tac_wp_pure_wp` with the reduct given up to an equation (used by the
tactics, which simplify the reduct). -/
theorem tac_wp_pure_wp' {φ : Prop} {e1 e2 e' : expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (heq : fill K e2 = e') (h : Δ' ⊢ WP e' @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  tac_wp_pure_wp (Hwp := Hwp) hφ hlater (heq ▸ h)

theorem tac_wp_pure_wp_lc' {φ : Prop} {e1 e2 e' : expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (heq : fill K e2 = e')
    (h : Δ' ⊢ iprop(£ 1 -∗ WP e' @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  tac_wp_pure_wp_later_credit (Hwp := Hwp) hφ hlater (heq ▸ h)

/-- Establish `PureWp` from a one-step `PureExec`. -/
theorem pure_exec_pure_wp {φ : Prop} {e e' : expr} (H : Language.PureExec φ 1 e e') :
    PureWp (G := G) (L := L) φ e e' where
  pure_wp_wp s E Φ K hφ := by
    have := Language.pureExec_fill (fill K) H
    exact wp_pure_step_later (φ := φ) (n := 1) hφ

/-- Establish `PureWp` for an expression `e` that reduces (in any number of
steps) to the value `v'`, given a WP for `e` itself. -/
theorem pure_wp_val (φ : Prop) (e : expr) (v' : val)
    (Hwp : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF), φ → iprop(▷ (£ 1 -∗ Φ v')) ⊢ WP e @ s; E {{ Φ }}) :
    PureWp (G := G) (L := L) φ e (Val v') where
  pure_wp_wp s E Φ K hφ := by
    refine .trans ?_ (wp_bind (fill K))
    exact Hwp s E (fun v => WP (fill K (Val v)) @ s; E {{ Φ }}) hφ

end classes

/-! ## Basic instances -/

section instances
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]

instance wp_snd (v1 v2 : val) : PureWp (G := G) (L := L) True (Snd (Val (PairV v1 v2))) (Val v2) :=
  pure_exec_pure_wp (pure_snd v1 v2)

instance wp_fst (v1 v2 : val) : PureWp (G := G) (L := L) True (Fst (Val (PairV v1 v2))) (Val v1) :=
  pure_exec_pure_wp (pure_fst v1 v2)

instance wp_recc (f x : binder) (erec : expr) :
    PureWp (G := G) (L := L) True (Rec f x erec) (Val (RecV f x erec)) :=
  pure_exec_pure_wp (pure_recc f x erec)

instance wp_pair (v1 v2 : val) :
    PureWp (G := G) (L := L) True (Pair (Val v1) (Val v2)) (Val (PairV v1 v2)) :=
  pure_exec_pure_wp (pure_pairc v1 v2)

instance wp_if_false (e1 e2 : expr) : PureWp (G := G) (L := L) True (If (Val #false) e1 e2) e2 :=
  pure_exec_pure_wp (pure_if_false e1 e2)

instance wp_if_true (e1 e2 : expr) : PureWp (G := G) (L := L) True (If (Val #true) e1 e2) e1 :=
  pure_exec_pure_wp (pure_if_true e1 e2)

/-- Rocq `wp_call` (a `Hint Extern` there; see the module docstring). -/
instance wp_call (v2 : val) (f x : binder) (e : expr) :
    PureWp (G := G) (L := L) True (App (Val (RecV f x e)) (Val v2))
      (subst' x v2 (subst' f (RecV f x e) e)) :=
  pure_exec_pure_wp (pure_beta f x e v2)

instance pure_wp_LiteralValue (l : List keyed_element) :
    PureWp (G := G) (L := L) True (LiteralValue l) (Val (LiteralValueV l)) :=
  pure_exec_pure_wp (pure_literal_value l)

instance pure_wp_SelectStmtClauses (d : Option expr) (cs : List comm_clause) :
    PureWp (G := G) (L := L) True (SelectStmtClauses d cs) (Val (SelectStmtClausesV d cs)) :=
  pure_exec_pure_wp (pure_select_stmt_clauses d cs)

variable [GoSemanticsFunctions] [go.PreSemantics]

instance wp_call_go_func (v2 : val) (f x : binder) (e : expr) :
    PureWp (G := G) (L := L) True (App (Val #(func.mk f x e)) (Val v2))
      (subst' x v2 (subst' f #(func.mk f x e) e)) := by
  have h : (#(func.mk f x e) : val) = RecV f x e := by
    rw [go.into_val_unfold func.t]
  rw [h]
  exact pure_exec_pure_wp (pure_beta f x e v2)

end instances

/-! ## Lemmas used by the tactics -/

section lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [ι : IrisGS_gen hlc expr GF]

theorem tac_wp_bind {Δ : IProp GF} {s : Stuckness} {E : CoPset} {K : List ectx_item} {e' : expr}
    {Φ : val → IProp GF}
    (H : Δ ⊢ WP e' @ s; E {{ v, WP (fill K (Val v)) @ s; E {{ Φ }} }}) :
    Δ ⊢ WP (fill K e') @ s; E {{ Φ }} :=
  H.trans (wp_bind (fill K))

theorem tac_wp_value {Δ : IProp GF} {s : Stuckness} {E : CoPset} {v : val} {Φ : val → IProp GF}
    (H : Δ ⊢ |={E}=> Φ v) : Δ ⊢ WP (Val v) @ s; E {{ Φ }} :=
  H.trans (wp_value_fupd (e := Val v) ⟨rfl⟩).2

theorem tac_wp_value_nofupd {Δ : IProp GF} {s : Stuckness} {E : CoPset} {v : val}
    {Φ : val → IProp GF} (H : Δ ⊢ Φ v) : Δ ⊢ WP (Val v) @ s; E {{ Φ }} :=
  H.trans <| fupd_intro.trans (wp_value_fupd (e := Val v) ⟨rfl⟩).2

theorem tac_wp_expr_simp {Δ : IProp GF} {s : Stuckness} {E : CoPset} {e e' : expr}
    {Φ : val → IProp GF} (h : Δ ⊢ WP e' @ s; E {{ Φ }}) (heq : e = e') :
    Δ ⊢ WP e @ s; E {{ Φ }} := heq ▸ h

theorem tac_add_hyp {PROP : Type _} [BI PROP] {Δ Δ' P Q : PROP}
    (hadd : iprop(Δ ∗ P) ⊣⊢ Δ') (h : Δ' ⊢ Q) : iprop(Δ ∗ P) ⊢ Q :=
  hadd.1.trans h

theorem tac_intro_hyp_wand {PROP : Type _} [BI PROP] {Δ Δ' P Q : PROP}
    (hadd : iprop(Δ ∗ P) ⊣⊢ Δ') (h : Δ' ⊢ Q) : Δ ⊢ iprop(P -∗ Q) :=
  wand_intro (hadd.1.trans h)

theorem tac_wp_true_elim {PROP : Type _} [BI PROP] [BIAffine PROP] {Δ P : PROP} (h : Δ ⊢ P) :
    Δ ⊢ iprop(⌜True⌝ -∗ P) :=
  wand_intro (sep_elim_left.trans h)

end lemmas

/-! ## Expression simplification -/

section simp_lemmas
variable [ext : ffi_syntax]

@[goose_wp_simp] theorem subst'_BAnon (v : val) (e : expr) : subst' BAnon v e = e := rfl
@[goose_wp_simp] theorem subst'_BNamed (x : String) (v : val) (e : expr) :
    subst' (BNamed x) v e = subst x v e := rfl

attribute [goose_wp_simp] subst subst_opt subst_keyed_elements subst_keyed_element subst_opt_key
  subst_element subst_comm_clauses subst_comm_clause

end simp_lemmas

simproc [goose_wp_simp] goose_reduceStrEq (( _ : String) = _) := String.reduceEq
simproc [goose_wp_simp] goose_reduceCtorEq (_ = _) := reduceCtorEq
open Lean Meta in
/-- Evaluate a closed `decide p` (e.g. comparisons of Go string literals in
`exception_seq`), by reduction. -/
simproc [goose_wp_simp] goose_reduceDecide (decide _) := fun e => do
  let_expr Decidable.decide p _ := e | return .continue
  if p.hasFVar then return .continue
  if p.hasMVar then return .continue
  let r ← withTransparency .default <| whnf e
  if r.isConstOf ``Bool.true ∨ r.isConstOf ``Bool.false then
    return .done { expr := r, proof? := some (mkExpectedPropHint (← mkEqRefl r) (← mkEq e r)) }
  return .continue

attribute [goose_wp_simp] List.foldr_cons List.foldr_nil List.foldl_cons List.foldl_nil
  List.zip_cons_cons List.zip_nil_left List.zip_nil_right

attribute [goose_wp_simp] _root_.decide_true _root_.decide_false

attribute [goose_wp_simp] ne_eq not_false_eq_true not_true_eq_false binder.BNamed.injEq
  _root_.and_self _root_.and_true _root_.true_and _root_.and_false _root_.false_and ite_true ite_false if_true if_false
  Bool.false_eq_true

/-! ## Meta-level helpers -/

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Names of the binders of a (∀-)type, in order. -/
private partial def binderNames : Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- Apply constant `c` to the arguments named in `args` (by binder name); all
other arguments are inferred by unification, and remaining instance-implicit
arguments are synthesized. Types of the given arguments are checked with
`isDefEq`. -/
def mkAppNamed (c : Name) (args : List (String × Expr)) : MetaM Expr := do
  let info ← getConstInfo c
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty ← instantiateTypeLevelParams info.toConstantVal us
  let names := binderNames ty
  let (mvs, bis, _) ← forallMetaTelescope ty
  -- arguments whose name starts with `!` are assigned without a type check (the
  -- kernel checks the final proof); they are assigned last
  let (unchecked, checked) := args.partition (·.1.startsWith "!")
  for (n, v) in checked do
    let some i := names.idxOf? (Name.mkSimple n) | throwError "mkAppNamed: {c} has no argument {n}"
    let mv := mvs[i]!
    let mvTy ← instantiateMVars (← inferType mv)
    let vTy ← inferType v
    unless ← isDefEq mvTy vTy do
      throwError "mkAppNamed: type mismatch for argument {n} of {c}:{indentExpr vTy}\n\
        expected{indentExpr mvTy}"
    unless ← isDefEq mv v do
      throwError "mkAppNamed: could not assign argument {n} of {c}"
  for i in [:mvs.size] do
    if bis[i]! == .instImplicit then
      let mv := mvs[i]!
      unless ← mv.mvarId!.isAssigned do
        let inst ← synthInstance (← instantiateMVars (← inferType mv))
        unless ← isDefEq mv inst do
          throwError "mkAppNamed: could not assign instance argument {i} of {c}"
  for (n, v) in unchecked do
    let n := (n.drop 1).toString
    let some i := names.idxOf? (Name.mkSimple n) | throwError "mkAppNamed: {c} has no argument {n}"
    mvs[i]!.mvarId!.assign v
  for i in [:mvs.size] do
    unless ← mvs[i]!.mvarId!.isAssigned do
      throwError "mkAppNamed: argument {names[i]!} of {c} could not be inferred"
  instantiateMVars (mkAppN (mkConst c us) mvs)

/-- A parsed GooseLang WP goal `Δ ⊢ WP (fill? e) @ s; E {{ Φ }}`. If the
expression is `fill Kl e` for an opaque (non-literal) evaluation context `Kl`,
then `tail` is `fill Kl` and `e` is the inner expression; the tactics then work
inside `e` and treat `Kl` as the outermost part of every evaluation context. -/
structure GooseWpGoal where
  /-- `Wp.wp` applied to its implicit and instance arguments. -/
  wpHead : Expr
  /-- The `IrisGS_gen` instance. -/
  ι : Expr
  /-- The `ffi_syntax` instance of the expression type. -/
  ext : Expr
  s : Expr
  E : Expr
  e : Expr
  Φ : Expr
  /-- `fill Kl` (partially applied) and `Kl`, for an opaque outer context `Kl`. -/
  tail : Option (Expr × Expr) := none

/-- Wrap an inner expression into the opaque outer context of the goal. -/
def GooseWpGoal.wrap (g : GooseWpGoal) (e : Expr) : Expr :=
  match g.tail with
  | none => e
  | some (fillKl, _) => mkApp fillKl e

def GooseWpGoal.mk' (g : GooseWpGoal) (e Φ : Expr) : Expr :=
  mkAppN g.wpHead #[g.s, g.E, g.wrap e, Φ]

/-- Parse `goal` as a WP over GooseLang expressions. -/
def parseGooseWp? (goal : Expr) : MetaM (Option GooseWpGoal) := do
  let goal ← instantiateMVars goal
  let goal := goal.consumeMData
  unless goal.isAppOfArity ``Iris.Wp.wp 9 do return none
  let args := goal.getAppArgs
  let exprTy := args[1]!
  let_expr Perennial.expr ext := exprTy.consumeMData | return none
  let self := args[4]!
  let ι := if self.isAppOf ``Iris.wp.def then self.getAppArgs.back! else self
  let e := args[7]!.consumeMData
  let (e, tail) :=
    if e.isAppOfArity ``Iris.ProgramLogic.EvContext.fill 5 then
      (e.getArg! 4, some (e.appFn!, e.getArg! 3))
    else (e, none)
  return some { wpHead := mkAppN goal.getAppFn args[:5], ι, ext,
                s := args[5]!, E := args[6]!, e, Φ := args[8]!, tail }

/-- Run `k` on the current Iris goal, which must be a GooseLang WP. -/
def runTacticGooseWp {α} (tacName : Name)
    (k : MVarId → IrisGoal → GooseWpGoal → ProofModeM α) : TacticM α :=
  ProofModeM.runTactic tacName fun mvar g => do
    let some wp ← parseGooseWp? g.goal
      | throwIPMError "the goal {g.goal} is not a GooseLang WP"
    k mvar g wp

/-- One evaluation-context item of a GooseLang expression: the item (as a
`ectx_item` expression) and the sub-expression in the hole. Mirrors
`fill_item` in `Perennial/GooseLang/Lang.lean`. -/
def extractEctxItem (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfR (← instantiateMVars e)
  let isVal (e : Expr) : MetaM (Option Expr) := do
    let e ← whnfR e
    match_expr e with
    | Perennial.expr.Val _ v => return some v
    | _ => return none
  let mk (n : Name) (ext : Expr) (args : Array Expr) : Expr :=
    mkAppN (mkConst n) (#[ext] ++ args)
  match_expr e with
  | Perennial.expr.App ext e1 e2 =>
    if let some v ← isVal e2 then return some (mk ``ectx_item.AppLCtx ext #[v], e1)
    else return some (mk ``ectx_item.AppRCtx ext #[e1], e2)
  | Perennial.expr.If ext e0 e1 e2 => return some (mk ``ectx_item.IfCtx ext #[e1, e2], e0)
  | Perennial.expr.Pair ext e1 e2 =>
    if let some v ← isVal e1 then return some (mk ``ectx_item.PairRCtx ext #[v], e2)
    else return some (mk ``ectx_item.PairLCtx ext #[e2], e1)
  | Perennial.expr.Fst ext e => return some (mk ``ectx_item.FstCtx ext #[], e)
  | Perennial.expr.Snd ext e => return some (mk ``ectx_item.SndCtx ext #[], e)
  | Perennial.expr.Primitive1 ext op e => return some (mk ``ectx_item.Primitive1Ctx ext #[op], e)
  | Perennial.expr.Primitive2 ext op e1 e2 =>
    if let some v ← isVal e1 then return some (mk ``ectx_item.Primitive2RCtx ext #[op, v], e2)
    else return some (mk ``ectx_item.Primitive2LCtx ext #[op, e2], e1)
  | Perennial.expr.ExternalOp ext op e => return some (mk ``ectx_item.ExternalOpCtx ext #[op], e)
  | Perennial.expr.CmpXchg ext e0 e1 e2 =>
    match ← isVal e0, ← isVal e1 with
    | some v0, some v1 => return some (mk ``ectx_item.CmpXchgRCtx ext #[v0, v1], e2)
    | some v0, none => return some (mk ``ectx_item.CmpXchgMCtx ext #[v0, e2], e1)
    | none, _ => return some (mk ``ectx_item.CmpXchgLCtx ext #[e1, e2], e0)
  | Perennial.expr.ResolveProph ext e1 e2 =>
    if let some v ← isVal e2 then return some (mk ``ectx_item.ResolveProphLCtx ext #[v], e1)
    else return some (mk ``ectx_item.ResolveProphRCtx ext #[e1], e2)
  | _ => return none

/-- `fill_item Ki e` at the meta level, producing constructor applications. -/
def fillItemExpr (Ki e : Expr) : MetaM Expr := do
  let Ki ← whnfR Ki
  let ext := Ki.getAppArgs[0]!
  let a := Ki.getAppArgs
  let mk (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let val (v : Expr) : Expr := mk ``Perennial.expr.Val #[v]
  match Ki.getAppFn.constName? with
  | some ``ectx_item.AppLCtx => return mk ``Perennial.expr.App #[e, val a[1]!]
  | some ``ectx_item.AppRCtx => return mk ``Perennial.expr.App #[a[1]!, e]
  | some ``ectx_item.IfCtx => return mk ``Perennial.expr.If #[e, a[1]!, a[2]!]
  | some ``ectx_item.PairLCtx => return mk ``Perennial.expr.Pair #[e, a[1]!]
  | some ``ectx_item.PairRCtx => return mk ``Perennial.expr.Pair #[val a[1]!, e]
  | some ``ectx_item.FstCtx => return mk ``Perennial.expr.Fst #[e]
  | some ``ectx_item.SndCtx => return mk ``Perennial.expr.Snd #[e]
  | some ``ectx_item.Primitive1Ctx => return mk ``Perennial.expr.Primitive1 #[a[1]!, e]
  | some ``ectx_item.Primitive2LCtx => return mk ``Perennial.expr.Primitive2 #[a[1]!, e, a[2]!]
  | some ``ectx_item.Primitive2RCtx => return mk ``Perennial.expr.Primitive2 #[a[1]!, val a[2]!, e]
  | some ``ectx_item.ExternalOpCtx => return mk ``Perennial.expr.ExternalOp #[a[1]!, e]
  | some ``ectx_item.CmpXchgLCtx => return mk ``Perennial.expr.CmpXchg #[e, a[1]!, a[2]!]
  | some ``ectx_item.CmpXchgMCtx => return mk ``Perennial.expr.CmpXchg #[val a[1]!, e, a[2]!]
  | some ``ectx_item.CmpXchgRCtx => return mk ``Perennial.expr.CmpXchg #[val a[1]!, val a[2]!, e]
  | some ``ectx_item.ResolveProphLCtx => return mk ``Perennial.expr.ResolveProph #[e, val a[1]!]
  | some ``ectx_item.ResolveProphRCtx => return mk ``Perennial.expr.ResolveProph #[a[1]!, e]
  | _ => throwError "fillItemExpr: unknown evaluation context item {Ki}"

/-- `fill K e` at the meta level (`K` innermost item first). -/
def fillExpr (K : List Expr) (e : Expr) : MetaM Expr :=
  K.foldlM (fun e Ki => fillItemExpr Ki e) e

/-- Quote a list of `ectx_item`s (innermost first), ending in the opaque tail
`tail` (default `[]`). -/
def quoteEctx (ext : Expr) (K : List Expr) (tail : Option Expr := none) : Expr :=
  let ty := mkApp (mkConst ``ectx_item) ext
  K.foldr (fun Ki acc => mkApp3 (mkConst ``List.cons [0]) ty Ki acc)
    (tail.getD (mkApp (mkConst ``List.nil [0]) ty))

/-- `quoteEctx` with the goal's opaque tail. -/
def GooseWpGoal.quoteK (g : GooseWpGoal) (K : List Expr) : Expr :=
  quoteEctx g.ext K (g.tail.map (·.2))

/-- A proof of `fill K e2 = wrap e'` from a proof `p? : fill_items K e2 = e'`
(`none` for `rfl`). -/
def GooseWpGoal.wrapEq (g : GooseWpGoal) (e' : Expr) (p? : Option Expr) : MetaM Expr := do
  match p?, g.tail with
  | none, _ => mkEqRefl (g.wrap e')
  | some p, none => pure p
  | some p, some (fillKl, _) => mkCongrArg fillKl p

/-- Find the *outermost* evaluation context `K` and sub-expression `e'` with
`fill K e' = e` such that `pred K e'` succeeds (Rocq `walk_expr`). Values are
never visited. -/
partial def findEctx {α} (e : Expr) (pred : List Expr → Expr → ProofModeM α) :
    ProofModeM (Option (α × List Expr × Expr)) :=
  go e []
where
  go (e : Expr) (K : List Expr) : ProofModeM (Option (α × List Expr × Expr)) := do
    let e' ← whnfR (← instantiateMVars e)
    if e'.isAppOf ``Perennial.expr.Val then return none
    if let some a ← observing? (pred K e) then return some (a, K, e)
    let some (Ki, e'') ← extractEctxItem e | return none
    go e'' (Ki :: K)

/-- All evaluation-context decompositions of `e`, outermost first. -/
partial def allEctx (e : Expr) : MetaM (List (List Expr × Expr)) :=
  go e [] []
where
  go (e : Expr) (K : List Expr) (acc : List (List Expr × Expr)) :
      MetaM (List (List Expr × Expr)) := do
    let e' ← whnfR (← instantiateMVars e)
    if e'.isAppOf ``Perennial.expr.Val then return acc.reverse
    let acc := (K, e) :: acc
    let some (Ki, e'') ← extractEctxItem e | return acc.reverse
    go e'' (Ki :: K) acc

/-- Simplify a GooseLang expression with the `goose_wp_simp` simp set, returning
the new expression and a proof of `e = e'` (or `none` if unchanged). -/
def gooseExprSimp (e : Expr) : MetaM (Expr × Option Expr) := do
  let some ext ← getSimpExtension? `goose_wp_simp
    | throwError "cannot find the `goose_wp_simp` simp set"
  let some procext ← Simp.getSimprocExtension? `goose_wp_simp
    | throwError "cannot find the `goose_wp_simp` simprocs"
  let theorems ← ext.getTheorems
  let procs ← procext.getSimprocs
  let ctx ← Simp.mkContext (simpTheorems := #[theorems]) (congrTheorems := ← getSimpCongrTheorems)
    (config := { beta := true, eta := true, zeta := true, proj := true, iota := true,
                 decide := false })
  let ⟨res, _⟩ ← Meta.simp e ctx (simprocs := #[procs])
  return (res.expr, res.proof?)

/-- Instance arguments `ext ffi interp sem gctx hlc GF G L` of a `goose_irisGS`
instance. -/
def gooseGSArgs (ι : Expr) : MetaM (Array Expr) := do
  let ι ← instantiateMVars ι
  let ι ← if ι.isAppOf ``goose_irisGS then pure ι else whnfR ι
  unless ι.isAppOfArity ``goose_irisGS 9 do
    throwError "the WP is not over the GooseLang `IrisGS_gen` instance `goose_irisGS`:{indentExpr ι}"
  -- `goose_irisGS` takes `ext ffi interp hlc GF sem gctx G L`; return them in the
  -- order of the section variables of this file: `ext ffi interp sem gctx hlc GF G L`
  let a := ι.getAppArgs
  return #[a[0]!, a[1]!, a[2]!, a[5]!, a[6]!, a[3]!, a[4]!, a[7]!, a[8]!]

/-- Is the goal's expression a value `Val v` (with no opaque outer context)? -/
def GooseWpGoal.isVal? (g : GooseWpGoal) : MetaM (Option Expr) := do
  if g.tail.isSome then return none
  let e ← whnfR (← instantiateMVars g.e)
  match_expr e with
  | Perennial.expr.Val _ v => return some v
  | _ => return none

/-- Is `e` a GooseLang value `Val v`? -/
def isGooseVal? (e : Expr) : MetaM (Option Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match_expr e with
  | Perennial.expr.Val _ v => return some v
  | _ => return none

/-- A pure step found in a WP goal. -/
structure PureStep where
  K : List Expr
  e1 : Expr
  φ : Expr
  e2 : Expr
  inst : Expr

/-- Find a `PureWp` instance for `e1`. -/
def synthPureWp (gs : Array Expr) (e1 : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let e2 ← mkFreshExprMVar (mkApp (mkConst ``Perennial.expr) gs[0]!)
  let ty ← mkAppOptM ``PureWp (gs.map some ++ #[some φ, some e1, some e2])
  let some inst ← synthInstance? ty | return none
  let ty ← instantiateMVars ty
  let args := ty.getAppArgs
  return some (args[gs.size]!, args[gs.size + 2]!, inst)

/-- Discharge the side condition `φ` of a pure step. `True` is solved
immediately; otherwise iris-lean's side-condition solver is tried, and if it
fails the condition becomes a new goal (unless `failOnUnsolved`). -/
def solvePureSideCondition (φ : Expr) (failOnUnsolved : Bool) : ProofModeM Expr := do
  let φ ← instantiateMVars φ
  if φ.isConstOf ``True then return mkConst ``True.intro
  iSolveSidecondition φ (failOnUnsolved := failOnUnsolved)

/-- Is `e` a string literal? -/
def strLit? (e : Expr) : MetaM (Option String) := do
  match (← whnfR e).consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- A binder literal: `some none` for `BAnon`, `some (some x)` for `BNamed "x"`. -/
def binderLit? (b : Expr) : MetaM (Option (Option String)) := do
  let b ← whnfR b
  if b.isAppOf ``binder.BAnon then return some none
  if b.isAppOfArity ``binder.BNamed 1 then
    if let some x ← strLit? (b.getArg! 0) then return some (some x)
  return none

/-- `subst x v e` computed at the meta level on GooseLang constructor terms
(definitionally equal to `Perennial.subst x v e`; non-constructor subterms are
left as `subst x v _`). -/
partial def substMeta (ext : Expr) (x : String) (xe v : Expr) (e : Expr) : MetaM Expr := do
  let e ← whnfR e
  let fallback := mkApp4 (mkConst ``Perennial.subst) ext xe v e
  let rec' := substMeta ext x xe v
  let mk (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext] ++ args)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Perennial.expr.Val, _ => return e
  | some ``Perennial.expr.Var, #[_, y] =>
    match ← strLit? y with
    | some y' => return (if y' == x then mk ``Perennial.expr.Val #[v] else e)
    | none => return fallback
  | some ``Perennial.expr.Rec, #[_, f, y, body] =>
    match ← binderLit? f, ← binderLit? y with
    | some fb, some yb =>
      if fb == some x ∨ yb == some x then return mk ``Perennial.expr.Rec #[f, y, body]
      else return mk ``Perennial.expr.Rec #[f, y, ← rec' body]
    | _, _ => return fallback
  | some ``Perennial.expr.App, #[_, a, b] => return mk ``Perennial.expr.App #[← rec' a, ← rec' b]
  | some ``Perennial.expr.If, #[_, a, b, c] =>
    return mk ``Perennial.expr.If #[← rec' a, ← rec' b, ← rec' c]
  | some ``Perennial.expr.Pair, #[_, a, b] => return mk ``Perennial.expr.Pair #[← rec' a, ← rec' b]
  | some ``Perennial.expr.Fst, #[_, a] => return mk ``Perennial.expr.Fst #[← rec' a]
  | some ``Perennial.expr.Snd, #[_, a] => return mk ``Perennial.expr.Snd #[← rec' a]
  | some ``Perennial.expr.Fork, #[_, a] => return mk ``Perennial.expr.Fork #[← rec' a]
  | some ``Perennial.expr.Primitive0, _ => return e
  | some ``Perennial.expr.Primitive1, #[_, op, a] =>
    return mk ``Perennial.expr.Primitive1 #[op, ← rec' a]
  | some ``Perennial.expr.Primitive2, #[_, op, a, b] =>
    return mk ``Perennial.expr.Primitive2 #[op, ← rec' a, ← rec' b]
  | some ``Perennial.expr.ExternalOp, #[_, op, a] =>
    return mk ``Perennial.expr.ExternalOp #[op, ← rec' a]
  | some ``Perennial.expr.CmpXchg, #[_, a, b, c] =>
    return mk ``Perennial.expr.CmpXchg #[← rec' a, ← rec' b, ← rec' c]
  | some ``Perennial.expr.NewProph, _ => return e
  | some ``Perennial.expr.ResolveProph, #[_, a, b] =>
    return mk ``Perennial.expr.ResolveProph #[← rec' a, ← rec' b]
  | _, _ => return fallback

/-- Evaluate the `subst'`/`subst` applications at the head of `e` with
`substMeta` (the result is definitionally equal to `e`). -/
partial def evalSubsts (ext : Expr) (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Perennial.subst' 4 then
    let b := e.getArg! 1
    let v := e.getArg! 2
    let body ← evalSubsts ext (e.getArg! 3)
    match ← binderLit? b with
    | some none => return body
    | some (some x) => return ← substMeta ext x (mkStrLit x) v body
    | none => return mkApp4 (mkConst ``Perennial.subst') ext b v body
  if e.isAppOfArity ``Perennial.subst 4 then
    let xe := e.getArg! 1
    let v := e.getArg! 2
    let body ← evalSubsts ext (e.getArg! 3)
    match ← strLit? xe with
    | some x => return ← substMeta ext x xe v body
    | none => return mkApp4 (mkConst ``Perennial.subst) ext xe v body
  return e

/-- Simplify the reduct `e2` of a step and fill the evaluation context `K`
around it: returns `fill K e2'` and a proof of `fill K e2 = fill K e2'` (only
the reduct is simplified; the context is already in normal form). -/
def simpReduct (ext : Expr) (K : List Expr) (e2 : Expr) : MetaM (Expr × Option Expr) := do
  -- substitutions are computed at the meta level (definitional, checked by the
  -- kernel); the rest is simplified with `goose_wp_simp`
  let e2s ← evalSubsts ext e2
  let (e2', p?) ← gooseExprSimp e2s
  let p? ← match p? with
    | none => if e2s == e2 then pure none else some <$> mkEqRefl e2s
    | some p => pure (some p)
  let filled ← fillExpr K e2'
  match p? with
  | none => return (filled, none)
  | some p =>
    let exprTy := mkApp (mkConst ``Perennial.expr) ext
    let f ← withLocalDeclD `x exprTy fun x => do mkLambdaFVars #[x] (← fillExpr K x)
    return (filled, some (← mkCongrArg f p))

/-- `(modality_laterN 1)` at the given BI. -/
def laterModality {u} (prop : Q(Type u)) (bi : Q(BI $prop)) : MetaM Q(Modality $prop $prop) :=
  mkAppOptM ``modality_laterN #[some prop, some (mkNatLit 1), some bi]

/-- Take one pure step in the WP goal `hyps ⊢ wp`. Returns the new context,
the new (simplified) expression, and a function turning a proof of the new goal
(`hyps' ⊢ WP e' ...`, or `hyps' ⊢ £ 1 -∗ WP e' ...` when `lc`) into a proof of
the old one. `pred` restricts the redexes considered. -/
def iWpPureStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (failOnUnsolved lc : Bool)
    (pred : Expr → MetaM Bool := fun _ => pure true) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let gs ← gooseGSArgs wp.ι
  let some (st, _, _) ← findEctx wp.e (fun K e1 => do
      unless ← pred e1 do throwError "skip"
      let some (φ, e2, inst) ← synthPureWp gs e1 | throwError "no PureWp instance"
      return ({ K, e1, φ, e2, inst } : PureStep))
    | throwIPMError "could not find a head subexpression with a known next step"
  let hφ ← solvePureSideCondition st.φ failOnUnsolved
  let ⟨ehyps', hyps', hlater⟩ ← iModAction (prop1 := prop) (bi1 := bi) hyps (← laterModality prop bi)
  let (e', heq?) ← simpReduct wp.ext st.K (← instantiateMVars st.e2)
  let heq ← wp.wrapEq e' heq?
  let Kq := wp.quoteK st.K
  let k := fun (h : Expr) => mkAppNamed (if lc then ``tac_wp_pure_wp_lc' else ``tac_wp_pure_wp')
    [("Hwp", st.inst), ("K", Kq), ("e1", st.e1), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ),
     ("hφ", hφ), ("hlater", hlater), ("e'", wp.wrap e'), ("!heq", heq),
     (if lc then "h" else "!h", h)]
  return ⟨ehyps', hyps', e', k⟩

/-- Simplify the expression of the WP goal with `goose_wp_simp`. Returns the new
(inner) expression and a function turning a proof of the new goal into a proof
of the old one, or `none` if nothing changed. -/
def iWpExprSimp (wp : GooseWpGoal) (Δ : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  let (e', p?) ← gooseExprSimp wp.e
  let some _ := p? | return none
  if e' == wp.e then return none
  let heq ← wp.wrapEq e' p?
  return some (e', fun h => mkAppNamed ``tac_wp_expr_simp
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e), ("e'", wp.wrap e'),
     ("!h", h), ("!heq", heq)])

/-- Turn the goal `hyps ⊢ WP (Val v) {{ Φ }}` into `hyps ⊢ Φ v` (Rocq
`iApply wp_value`), continuing with `k` on the new conclusion. -/
def iWpValue {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (v : Expr)
    (k : Expr → ProofModeM Expr) : ProofModeM Expr := do
  let goal := (mkApp wp.Φ v).headBeta
  let pf ← k goal
  mkAppNamed ``tac_wp_value_nofupd
    [("Δ", ehyps), ("s", wp.s), ("E", wp.E), ("v", v), ("Φ", wp.Φ), ("!H", pf)]

/-- Repeatedly take pure steps (`wp_pures`); steps whose side condition cannot
be discharged automatically are not taken. When the expression becomes a value
`v`, the WP is replaced by `Φ v`, and if that is again a WP, stepping continues. -/
partial def iWpPures {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (simpFirst : Bool := true) : ProofModeM Expr := do
  if simpFirst then
    if let some (e', k) ← iWpExprSimp wp ehyps then
      return ← k (← iWpPures hyps { wp with e := e' } (simpFirst := false))
  if let some v ← wp.isVal? then
    return ← iWpValue hyps wp v fun goal => do
      if let some wp' ← parseGooseWp? goal then iWpPures hyps wp'
      else addBIGoal hyps goal
  let saved ← saveState
  match ← observing? (iWpPureStep hyps wp (failOnUnsolved := true) (lc := false)) with
  | some ⟨_, hyps', e', k⟩ =>
    -- do not loop on an expression that steps to itself (e.g. `rec: f <> := f #()`)
    if e' == wp.e then
      saved.restore
      return ← addBIGoal hyps (wp.mk' wp.e wp.Φ)
    let pf ← iWpPures hyps' { wp with e := e' } (simpFirst := false)
    k pf
  | none => addBIGoal hyps (wp.mk' wp.e wp.Φ)

/-- Finish a goal `hyps ⊢ WP e {{ Φ }}`: if `e` is a value, replace the WP by
`Φ v`; otherwise leave it. -/
def iWpFinish {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) : ProofModeM Expr := do
  if let some v ← wp.isVal? then
    iWpValue hyps wp v (addBIGoal hyps ·)
  else
    addBIGoal hyps (wp.mk' wp.e wp.Φ)

/-- Bind the evaluation context `K` around `e'` in the goal
`Δ ⊢ WP (fill K e') {{ Φ }}`: `k` is given the new conclusion
`WP e' {{ v, WP (fill K (Val v)) {{ Φ }} }}` and must prove it from `Δ`. -/
def iWpBindCore (Δ : Expr) (wp : GooseWpGoal) (K : List Expr) (e' : Expr)
    (k : Expr → ProofModeM Expr) : ProofModeM Expr := do
  if K.isEmpty && wp.tail.isNone then return ← k (wp.mk' e' wp.Φ)
  let valTy := mkApp (mkConst ``Perennial.val) wp.ext
  let Φ' ← withLocalDeclD `v valTy fun v => do
    let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.expr.Val) wp.ext v)
    mkLambdaFVars #[v] (wp.mk' filled wp.Φ)
  let pf ← k ({ wp with tail := none }.mk' e' Φ')
  mkAppNamed ``tac_wp_bind [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("K", wp.quoteK K),
    ("e'", e'), ("Φ", wp.Φ), ("!H", pf)]

/-- Rocq `wp_bind_next`: the evaluation context to bind for the "next"
operation (a function call, possibly curried, or the innermost expression that
is not an evaluation-context constructor). -/
def findBindNext (e : Expr) : MetaM (Option (List Expr × Expr)) := do
  let mut bindCtx : Option (List Expr × Expr) := none
  let mut isCallSoFar := true
  let mut cur := e
  let mut K : List Expr := []
  repeat
    let cur' ← whnfR (← instantiateMVars cur)
    if cur'.isAppOf ``Perennial.expr.Val then break
    let isAppVal ← match_expr cur' with
      | Perennial.expr.App _ _ e2 => pure (← isGooseVal? e2).isSome
      | _ => pure false
    if isAppVal then
      unless isCallSoFar do bindCtx := some (K, cur)
      isCallSoFar := true
    else
      bindCtx := some (K, cur)
      isCallSoFar := false
    let some (Ki, cur'') ← extractEctxItem cur | break
    K := Ki :: K
    cur := cur''
  return bindCtx

/-- Elaborate a GooseLang expression pattern (in goose expression mode). -/
def elabGoosePattern (stx : Term) (ext : Expr) : TermElabM Expr := do
  let ty := mkApp (mkConst ``Perennial.expr) ext
  let e ← Term.elabTermEnsuringType (← `(gl($stx))) ty
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  instantiateMVars e

end tactics

/-! ## The tactics -/

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_pures` takes all pure steps at the head of the WP goal: it repeatedly
finds the outermost subexpression in evaluation position that has a `PureWp`
instance (beta reduction, `if` on a literal boolean, projections of pairs, Go
instructions with a deterministic pure semantics, `exception_seq`, ...) and
steps it, simplifying substitutions. A step whose side condition cannot be
solved automatically is not taken. When the expression becomes a value `v`,
`WP v {{ Φ }}` is replaced by `Φ v`. Never fails (does nothing on a non-WP goal).

Example: `WP (let: "x" := #(W64 1) in "x") {{ Φ }}` becomes `Φ #(W64 1)`. -/
elab "wp_pures" : tactic => do
  let some g := parseIrisGoal? (← instantiateMVars (← (← getMainGoal).getType)) | return
  unless (← parseGooseWp? g.goal).isSome do return
  runTacticGooseWp `wp_pures fun mvar g wp => do
    mvar.assign (← iWpPures g.hyps wp)

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_expr_simp` simplifies the expression of the WP goal with the
`goose_wp_simp` simp set (substitutions, evaluation contexts, closed `decide`s). -/
elab "wp_expr_simp" : tactic =>
  runTacticGooseWp `wp_expr_simp fun mvar g wp => do
    match ← iWpExprSimp wp g.e with
    | some (e', k) => mvar.assign (← k (← addBIGoal g.hyps (wp.mk' e' wp.Φ)))
    | none => mvar.assign (← addBIGoal g.hyps g.goal)

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_pure` takes a single pure step (see `wp_pures`); a side condition that
cannot be discharged automatically is left as a new goal. On a value, it
replaces `WP v {{ Φ }}` by `Φ v`. `wp_pure e` only steps a redex matching the
GooseLang pattern `e` (goose expression mode, e.g. `wp_pure (if: _ then _ else _)`). -/
syntax (name := wpPureTac) "wp_pure" (ppSpace colGt term:max)? : tactic

open Lean Elab Tactic Meta Qq Iris.ProofMode in
@[tactic wpPureTac] def evalWpPure : Tactic := fun stx => do
  let pat? : Option Term := if stx[1].isNone then none else some ⟨stx[1][0]⟩
  runTacticGooseWp `wp_pure fun mvar g wp => do
    if let some v ← wp.isVal? then
      mvar.assign (← iWpValue g.hyps wp v (addBIGoal g.hyps ·))
      return
    let pred ← match pat? with
      | none => Pure.pure (fun _ => Pure.pure true : Expr → MetaM Bool)
      | some pat => do
        let p ← elabGoosePattern pat wp.ext
        Pure.pure (fun e => withReducible (withNewMCtxDepth (isDefEq e p)) : Expr → MetaM Bool)
    let ⟨_, hyps', e', k⟩ ← iWpPureStep g.hyps wp (failOnUnsolved := false) (lc := false) pred
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Internal: one pure step, keeping the later credit: the new goal is
`£ 1 -∗ WP e' {{ Φ }}`. -/
elab "wp_pure_lc_core" : tactic =>
  runTacticGooseWp `wp_pure_lc fun mvar g wp => do
    let ⟨_, hyps', _, k⟩ ← iWpPureStep g.hyps wp (failOnUnsolved := false) (lc := true)
    -- read the new conclusion `£ 1 -∗ WP e' {{ Φ }}` off the lemma
    let hT ← mkFreshTypeMVar
    let h ← mkFreshExprMVar hT
    let pf ← k h
    let T ← whnfR (← instantiateMVars hT)
    let concl := T.getAppArgs.back!
    let g' ← addBIGoal hyps' concl
    h.mvarId!.assign g'
    mvar.assign pf

/-- `wp_pure_lc H` takes one pure step (see `wp_pure`) and introduces the
later credit `£ 1` it produces as the hypothesis `H`. -/
macro "wp_pure_lc " H:ident : tactic => `(tactic| (wp_pure_lc_core; iintro $H:ident))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_bind e` focuses the WP goal `WP K[e'] {{ Φ }}` on the outermost
subexpression `e'` in evaluation position matching the GooseLang pattern `e`
(goose expression mode, `_` for holes), producing
`WP e' {{ v, WP K[v] {{ Φ }} }}`.

`wp_bind` (no argument) is Rocq's `wp_bind_next`: it focuses on the next
"interesting" operation, i.e. the outermost (possibly curried) call
`f v1 ... vn` with value arguments, or else the innermost expression that is not
an evaluation-context constructor. It does nothing if that is the whole
expression.

Example: `wp_bind (if: _ then _ else _)`. -/
syntax (name := wpBindTac) "wp_bind" (ppSpace colGt term:max)? : tactic

open Lean Elab Tactic Meta Qq Iris.ProofMode in
@[tactic wpBindTac] def evalWpBind : Tactic := fun stx => do
  let pat? : Option Term := if stx[1].isNone then none else some ⟨stx[1][0]⟩
  runTacticGooseWp `wp_bind fun mvar g wp => do
    let res ← match pat? with
      | some pat => do
        let p ← elabGoosePattern pat wp.ext
        let some ((), K, e') ← findEctx wp.e (fun _ e => do
            unless ← withReducible (isDefEq e p) do throwError "no match"
            return ())
          | throwIPMError "could not find a subexpression in evaluation position matching {p}"
        Pure.pure (some (K, e'))
      | none => findBindNext wp.e
    match res with
    | none => mvar.assign (← addBIGoal g.hyps g.goal)
    | some ([], _) =>
      if wp.tail.isNone then mvar.assign (← addBIGoal g.hyps g.goal)
      else mvar.assign (← iWpBindCore g.e wp [] wp.e (addBIGoal g.hyps ·))
    | some (K, e') =>
      mvar.assign (← iWpBindCore g.e wp K e' (addBIGoal g.hyps ·))

section call_lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : gooseGlobalGS hlc GF] [L : gooseLocalGS GF]

/-- Rocq `tac_wp_rec`: call a function value `fv` that unfolds to
`rec: f x := e`. The recursive occurrences of `f` are replaced by the folded `fv`. -/
theorem tac_wp_call' {fv v2 : val} {f x : binder} {e e' : expr} (hfv : fv = RecV f x e)
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hlater : Δ ⊢ ▷ Δ') (heq : fill K (subst' x v2 (subst' f fv e)) = e')
    (h : Δ' ⊢ WP e' @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val fv) (Val v2))) @ s; E {{ Φ }} := by
  subst hfv
  exact tac_wp_pure_wp' (Hwp := wp_call (G := G) (L := L) v2 f x e) trivial hlater heq h

theorem tac_wp_call_lc' {fv v2 : val} {f x : binder} {e e' : expr} (hfv : fv = RecV f x e)
    {K : List ectx_item} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hlater : Δ ⊢ ▷ Δ') (heq : fill K (subst' x v2 (subst' f fv e)) = e')
    (h : Δ' ⊢ iprop(£ 1 -∗ WP e' @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K (App (Val fv) (Val v2))) @ s; E {{ Φ }} := by
  subst hfv
  exact tac_wp_pure_wp_lc' (Hwp := wp_call (G := G) (L := L) v2 f x e) trivial hlater heq h

end call_lemmas

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Find a call `App (Val fv) (Val v)` where `fv` unfolds (with default
transparency) to `RecV f x e`, and take the beta step. -/
def iWpCallStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (lc : Bool := false) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let some ((fv, v2, f, x, body), K, _) ← findEctx wp.e (fun _ e => do
      let e ← whnfR e
      let_expr Perennial.expr.App _ e1 e2 := e | throwError "not an application"
      let some fv ← isGooseVal? e1 | throwError "not a value"
      let some v2 ← isGooseVal? e2 | throwError "not a value"
      let fv' ← whnf fv
      let_expr Perennial.val.RecV _ f x body := fv' | throwError "not a function"
      return (fv, v2, f, x, body))
    | throwIPMError "could not find a function call expression at the head"
  let ⟨ehyps', hyps', hlater⟩ ← iModAction (prop1 := prop) (bi1 := bi) hyps (← laterModality prop bi)
  let s1 ← mkAppM ``subst' #[f, fv, body]
  let s2 ← mkAppM ``subst' #[x, v2, s1]
  let (e', heq?) ← simpReduct wp.ext K s2
  let heq ← wp.wrapEq e' heq?
  let hfv ← mkEqRefl fv
  let k := fun (h : Expr) => mkAppNamed (if lc then ``tac_wp_call_lc' else ``tac_wp_call')
    [("hfv", hfv), ("v2", v2), ("f", f), ("x", x), ("e", body), ("K", wp.quoteK K),
     ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("hlater", hlater), ("e'", wp.wrap e'),
     ("!heq", heq), (if lc then "h" else "!h", h)]
  return ⟨ehyps', hyps', e', k⟩

end tactics

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Internal: one beta step of a function call whose head is a constant or
`RecV` (no `wp_pures` afterwards). -/
elab "wp_call_core" : tactic =>
  runTacticGooseWp `wp_call fun mvar g wp => do
    let ⟨_, hyps', e', k⟩ ← iWpCallStep g.hyps wp
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Internal: `wp_call_core`, keeping the later credit. -/
elab "wp_call_lc_core" : tactic =>
  runTacticGooseWp `wp_call_lc fun mvar g wp => do
    let ⟨_, hyps', _, k⟩ ← iWpCallStep g.hyps wp (lc := true)
    let hT ← mkFreshTypeMVar
    let h ← mkFreshExprMVar hT
    let pf ← k h
    let T ← whnfR (← instantiateMVars hT)
    let g' ← addBIGoal hyps' T.getAppArgs.back!
    h.mvarId!.assign g'
    mvar.assign pf

/-- `wp_call_lc H` is `wp_call`, introducing the later credit of the beta step
as `H`. -/
macro "wp_call_lc " H:ident : tactic => `(tactic| (wp_call_lc_core; iintro $H:ident; wp_pures))

/-- `wp_call` calls the function at the head of the WP goal: it finds the
outermost application `fv v` in evaluation position whose function value `fv`
unfolds to a `rec:`/`λ:` value (e.g. a generated `«Fooⁱᵐᵖˡ»` constant), takes
the beta step (discarding the later credit) and then runs `wp_pures`. -/
macro "wp_call" : tactic => `(tactic| (wp_call_core; wp_pures))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Internal core of `wp_apply` (see `wp_apply_core`). -/
elab "wp_apply_raw " colGt pmt:pmTerm : tactic => do
  let pmt ← liftMacroM <| PMTerm.parse pmt
  ProofModeM.runTactic `wp_apply fun mvar {prop, bi, hyps, goal, ..} => do
    let some wp ← parseGooseWp? goal | throwIPMError "the goal {goal} is not a GooseLang WP"
    let ⟨ehypsP, hypsP, p, A, posePf⟩ ← iHave hyps goal pmt true
    let Δ : Q($prop) := q(iprop($ehypsP ∗ □?$p $A))
    -- try the `wp_bind_next` position first (as Rocq does), then every position,
    -- outermost first
    let next := (← findBindNext wp.e).toList
    for (K, e') in next ++ (← allEctx wp.e) do
      if let some pf ← observing? (iWpBindCore Δ wp K e' (fun goal' => iApply hypsP p A goal')) then
        mvar.assign (mkApp posePf pf).headBeta
        return
    throwIPMError "cannot apply {A} to any subexpression in evaluation position of{indentExpr wp.e}"

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- Internal: post-processing of the goals produced by `wp_apply_raw`: strip a
leading `▷`, and solve trivial `True`/`⌜True⌝`/`emp` goals (Rocq
`try iNext; try solve_bi_true`). -/
elab "wp_apply_post" : tactic => do
  let gs ← getGoals
  let mut out := []
  for mv in gs do
    if ← mv.isAssigned then continue
    let ty ← instantiateMVars (← mv.getType)
    unless isIrisGoal ty do
      out := out ++ [mv]; continue
    setGoals [mv]
    evalTactic (← `(tactic| try inext))
    let mut solved := false
    if let [mv'] ← getGoals then
      if let some g := parseIrisGoal? (← instantiateMVars (← mv'.getType)) then
        let goal ← whnfR (← instantiateMVars g.goal)
        let isTriv := goal.isAppOfArity ``BIBase.emp 2 ||
          (goal.isAppOfArity ``BIBase.pure 3 && (goal.getArg! 2).isConstOf ``True)
        if isTriv then
          if let some _ ← observing? (evalTactic (← `(tactic| ipureintro; trivial))) then
            solved := true
          else if let some _ ← observing? (evalTactic (← `(tactic| iempintro))) then
            solved := true
        -- `True -∗ P`: drop the premise (Rocq `tac_wp_true_elim`)
        if goal.isAppOfArity ``BIBase.wand 4 then
          let lhs ← whnfR (goal.getArg! 2)
          if lhs.isAppOfArity ``BIBase.pure 3 && (lhs.getArg! 2).isConstOf ``True then
            evalTactic (← `(tactic| iintro -))
    out := out ++ (← getGoals)
  setGoals out

/-- `wp_apply_core lem` (Rocq `wp_apply_core`) applies the specification `lem`
(a Lean lemma or an Iris hypothesis, optionally specialized with
`lem $$ spat1 spat2 ...`) to the WP goal. The conclusion of `lem` must be a WP
(typically `lem` is a Texan triple `{{ P }} e {{ x, RET v; Q }}`); `lem` is
applied to the outermost subexpression `e'` in evaluation position for which
this succeeds, binding the surrounding evaluation context. Premises become new
goals; a leading `▷` on a goal is stripped and trivial `True` goals are closed.
The last goal is the continuation, e.g. `∀ x, Q -∗ WP K[v] {{ Φ }}`.

Unlike `wp_apply` (in `Perennial/Golang/Theory/Auto.lean`), this does no
`is_pkg_init` solving, introduction or automation. -/
macro "wp_apply_core " pmt:pmTerm : tactic =>
  `(tactic| focus ((wp_apply_raw $pmt) <;> wp_apply_post))

end Perennial
