/-
Port of `new/golang/theory/mem.v`: atomic WPs on typed points-to, the
`Access`/`AccessStrict` classes for accessing (struct field) points-to facts,
and the typed memory tactics `wp_load`, `wp_store`, `wp_alloc`,
`wp_alloc_auto`.

`Access`/`AccessStrict` are iris-lean `ipm_class`es, searched with the proof
mode's Rocq-style typeclass search (which can instantiate metavariables), the
analogue of Rocq's `Hint Mode Access + ! ! - -`. The last two parameters are
`outParam`s (Rocq: `-`).
-/
import Perennial.Golang.Theory.Predeclared

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section goose_lang
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

/-- Atomic operations on a typed points-to. -/
class AtomicWps (V : Type) [TypedPointsto (GF := GF) V] [ZeroVal V] : Prop where
  wp_cmpxchg_fail : ∀ (l : loc) (v' v1 v2 : V) (dq : DFrac) (s : Stuckness) (E : CoPset),
    v' ≠ v1 →
    {{ ▷ (l ↦{dq} v' : IProp GF) }} (CmpXchg (Val #l) (Val #v1) (Val #v2)) @ s; E
    {{ RET (PairV #v' #false); l ↦{dq} v' }}
  wp_cmpxchg_suc : ∀ (l : loc) (v' v1 v2 : V) (s : Stuckness) (E : CoPset),
    v' = v1 →
    {{ ▷ (l ↦ v' : IProp GF) }} (CmpXchg (Val #l) (Val #v1) (Val #v2)) @ s; E
    {{ RET (PairV #v' #true); l ↦ v2 }}
  wp_atomic_load : ∀ (s : Stuckness) (E : CoPset) (l : loc) (dq : DFrac) (v : V),
    {{ ▷ (l ↦{dq} v : IProp GF) }} (Load (Val #l)) @ s; E {{ RET #v; l ↦{dq} v }}
  wp_atomic_swap : ∀ (s : Stuckness) (E : CoPset) (l : loc) (v v' : V),
    {{ (l ↦ v : IProp GF) }} (AtomicSwap (Val #l) (Val #v')) @ s; E {{ RET #v; l ↦ v' }}

export AtomicWps (wp_cmpxchg_fail wp_cmpxchg_suc wp_atomic_load wp_atomic_swap)

/-- Prove `AtomicWps V` for a type whose typed points-to is
`heap_pointsto l dq #v` (Rocq `solve_atomic_wps`). -/
macro "solve_atomic_wps" : tactic => `(tactic| (
  constructor
  all_goals try simp only [typed_pointsto_unseal, typed_pointsto_wrap, typed_pointsto_def_heap]
  · intro l v' v1 v2 dq s E Hne
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, >%Hnn⟩
    iapply Perennial.wp_cmpxchg_fail l dq #v' #v1 #v2 (fun h => Hne (go.into_val_inj h)) $$ Hl
    inext; iintro Hl
    iapply HΦ; iframe Hl; ipureintro; exact Hnn
  · intro l v' v1 v2 s E Heq
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, >%Hnn⟩
    iapply Perennial.wp_cmpxchg_suc l #v1 #v2 #v' (congrArg _ Heq) $$ Hl
    inext; iintro Hl
    iapply HΦ; iframe Hl; ipureintro; exact Hnn
  · intro s E l dq v
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, >%Hnn⟩
    iapply Perennial.wp_load l dq #v $$ Hl
    inext; iintro Hl
    iapply HΦ; iframe Hl; ipureintro; exact Hnn
  · intro s E l v v'
    iintro %Φ Hl HΦ
    icases Hl with ⟨Hl, %Hnn⟩
    iapply Perennial.wp_atomic_swap l #v #v' $$ Hl
    inext; iintro Hl
    iapply HΦ; iframe Hl; ipureintro; exact Hnn))

instance atomic_wps_uint64 : AtomicWps (GF := GF) w64 := by solve_atomic_wps
instance atomic_wps_uint32 : AtomicWps (GF := GF) w32 := by solve_atomic_wps
instance atomic_wps_uint16 : AtomicWps (GF := GF) w16 := by solve_atomic_wps
instance atomic_wps_uint8 : AtomicWps (GF := GF) w8 := by solve_atomic_wps
instance atomic_wps_bool : AtomicWps (GF := GF) Bool := by solve_atomic_wps
instance atomic_wps_loc : AtomicWps (GF := GF) loc := by solve_atomic_wps

end goose_lang

/-! ## Access to (sub-)points-to facts -/

/-- `AccessStrict A A' P P'`: from `P` one can take out `A`, and putting back
`A'` gives `P'` (e.g. a struct field points-to from a struct points-to). -/
@[ipm_class]
class AccessStrict {PROP : Type _} [BI PROP] (A A' : PROP) (P P' : outParam PROP) : Prop where
  access_strict : P ⊢ A ∗ (A' -∗ P')

/-- The reflexive-transitive closure of `AccessStrict`. -/
@[ipm_class]
class Access {PROP : Type _} [BI PROP] (A A' P : PROP) (P' : outParam PROP) : Prop where
  access : P ⊢ A ∗ (A' -∗ P')

export AccessStrict (access_strict)
export Access (access)

@[ipm_backtrack]
instance access_transitive {PROP : Type _} [BI PROP] {Q P P' Q' A A' : PROP}
    [h1 : AccessStrict A A' P P'] [h2 : Access P P' Q Q'] : Access A A' Q Q' where
  access := by
    iintro H
    icases h2.access $$ H with ⟨H, Hwand⟩
    icases h1.access_strict $$ H with ⟨H, Hwand'⟩
    iframe H
    iintro H
    iapply Hwand
    iapply Hwand' $$ H

instance access_trivial {PROP : Type _} [BI PROP] (P P' : PROP) : Access P P' P P' where
  access := by iintro H; iframe H; iintro H; iexact H

/-! ## Tactic lemmas -/

section tac_lemmas
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [GoSemanticsFunctions] [go.PreSemantics]

theorem access_split {Δ Δ' P A : IProp GF} {p : Bool} [h : Access A A P P]
    (hsplit : Δ ⊣⊢ Δ' ∗ iprop(□?p P)) : Δ ⊢ A ∗ (A -∗ Δ) := by
  cases p
  · have hsplit : Δ ⊣⊢ Δ' ∗ P := hsplit
    iintro HΔ
    icases hsplit.1 $$ HΔ with ⟨HΔ', HP⟩
    icases h.access $$ HP with ⟨HA, Hclose⟩
    iframe HA
    iintro HA
    iapply hsplit.2
    iframe HΔ'
    iapply Hclose $$ HA
  · have hsplit : Δ ⊣⊢ Δ' ∗ iprop(□ P) := hsplit
    iintro HΔ
    icases hsplit.1 $$ HΔ with ⟨HΔ', #HP⟩
    icases h.access $$ HP with ⟨HA, -⟩
    iframe HA
    iintro -
    iapply hsplit.2
    iframe HΔ' HP

theorem tac_wp_load {V : Type} {t : go.type} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List ectx_item} {l : loc} {v : V} {dq : DFrac}
    {Δ Δ' P : IProp GF} {p : Bool} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    [hacc : Access (l ↦{dq} v) (l ↦{dq} v) P P]
    (hsplit : Δ ⊣⊢ Δ' ∗ iprop(□?p P)) (h : Δ ⊢ WP (fill K (Val #v)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoLoad t))) (Val #l))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  refine (access_split (h := hacc) hsplit).trans ?_
  iintro ⟨HA, Hclose⟩
  iapply IntoValTyped.wp_load (t := t) l dq v $$ HA
  inext
  iintro HA
  iapply h
  iapply Hclose $$ HA

theorem tac_wp_store {V : Type} {t : go.type} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List ectx_item} {l : loc} {v w : V}
    {Δ Δ' Δ'' P P' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    [hacc : Access (l ↦ v) (l ↦ w) P P']
    (hsplit : Δ ⊣⊢ Δ' ∗ P) (hadd : Δ' ∗ P' ⊣⊢ Δ'')
    (h : Δ'' ⊢ WP (fill K (Val #())) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoStore t))) (Val (PairV #l #w)))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  refine hsplit.1.trans ?_
  iintro ⟨HΔ', HP⟩
  icases hacc.access $$ HP with ⟨HA, Hclose⟩
  iapply IntoValTyped.wp_store (t := t) l v w $$ HA
  inext
  iintro HA
  iapply h
  iapply hadd.1
  iframe HΔ'
  iapply Hclose $$ HA

theorem tac_wp_alloc {V : Type} {t : go.type} [ZeroVal V] [tpt : TypedPointsto (GF := GF) V]
    [IntoValTyped (GF := GF) V t] {K : List ectx_item} {v : V}
    {Δ : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (h : ∀ l : loc, Δ ∗ (l ↦ v) ⊢ WP (fill K (Val #l)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val (GoInstruction (GoAlloc t))) (Val #v))) @ s; E {{ Φ }} := by
  refine .trans ?_ (wp_bind (fill K))
  iintro HΔ
  iapply IntoValTyped.wp_alloc (t := t) v
  · itrivial
  inext
  iintro %l Hl
  iapply h l
  iframe

end tac_lemmas

/-! ## The memory tactics -/

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- If `e` is `#x` (`into_val x`), return `(V, x)`. -/
def isIntoVal? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let e := e.consumeMData
  if e.isAppOfArity ``GoGlobalContext.into_val 4 then
    return some (e.getArg! 2, e.getArg! 3)
  return none

/-- If `e` is `Val (GoInstruction i)` applied to `arg` with `i` satisfying
`instr`, return `(i, arg)`. -/
def isGoInstrApp? (e : Expr) (instr : Name) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfR (← instantiateMVars e)
  let_expr Perennial.expr.App _ f arg := e | return none
  let some fv ← isGooseVal? f | return none
  let fv ← whnfR fv
  let_expr Perennial.val.GoInstruction _ i := fv | return none
  let i ← whnfR i
  unless i.isAppOf instr do return none
  let some argv ← isGooseVal? arg | return none
  return some (i, argv)

/-- All hypotheses of `hyps`: `(name, ivar, p, ty)`. -/
def hypsList {u} {prop : Q(Type u)} {bi : Q(BI $prop)} :
    ∀ {e}, Hyps bi e → List (Name × IVarId × Q(Bool) × Q($prop))
  | _, .emp _ => []
  | _, .hyp _ name ivar p ty _ => [(name, ivar, p, ty)]
  | _, .sep _ _ _ _ lhs rhs => hypsList rhs ++ hypsList lhs

/-- The typed points-to `@typed_pointsto GF V inst l v dq`, with fresh
metavariables for `V`, the `TypedPointsto` instance, `v` (unless given) and
`dq` (unless given). -/
def mkTypedPointstoMVars (GF l : Expr) (V? v? dq? : Option Expr) :
    MetaM (Expr × Expr × Expr × Expr × Expr) := do
  let V ← match V? with | some V => pure V | none => mkFreshExprMVar (mkSort (mkLevelSucc .zero))
  let instTy ← mkAppOptM ``TypedPointsto #[some GF, some V]
  let inst ← mkFreshExprMVar instTy
  let v ← match v? with | some v => pure v | none => mkFreshExprMVar V
  let dq ← match dq? with | some dq => pure dq | none => mkFreshExprMVar (mkConst ``DFrac)
  let pt ← mkAppOptM ``typed_pointsto #[some GF, some V, some inst, some l, some v, some dq]
  return (pt, V, inst, v, dq)

/-- Search for `Access A A' P ?P'` with the proof mode's typeclass search. -/
def synthAccess (A A' P : Expr) : ProofModeM (Option (Expr × Expr)) := do
  let P' ← mkFreshExprMVar (← inferType P)
  let ty ← mkAppM ``Access #[A, A', P, P']
  match ← ProofMode.trySynthInstance ty with
  | .some (inst, _) => return some (inst, ← instantiateMVars P')
  | _ => return none

/-- One `wp_load` step: find `![t] #l` in evaluation position and a hypothesis
`P` (spatial or intuitionistic) with `Access (l ↦{dq} v) (l ↦{dq} v) P P`;
the load returns `#v` and keeps the context. -/
def iWpLoadStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let some ((t, l), K, _) ← findEctx wp.e (fun _ e => do
      let some (i, lv) ← isGoInstrApp? e ``go_instruction.GoLoad | throwError "no"
      let some (_, l) ← isIntoVal? lv | throwError "no"
      return (i.getArg! 1, l))
    | throwIPMError "could not find a load `![t] #l`"
  let GF := (← gooseGSArgs wp.ι)[6]!
  for (_, ivar, p, P) in hypsList hyps do
    let saved ← saveState
    let (A, V, inst, v, dq) ← mkTypedPointstoMVars GF l none none none
    if let some (hacc, P') ← synthAccess A A P then
      if ← isDefEq P' P then
        let r := hyps.remove true ivar
        let v ← instantiateMVars v
        let vv ← mkAppOptM ``GoGlobalContext.into_val #[none, none, some (← instantiateMVars V), some v]
        let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.expr.Val) wp.ext vv)
        let k := fun (h : Expr) => do
          let V ← instantiateMVars V
          let inst ← instantiateMVars inst
          mkAppNamed ``tac_wp_load
            [("V", V), ("t", t), ("K", wp.quoteK K), ("l", l), ("v", v),
             ("dq", ← instantiateMVars dq), ("Δ", ehyps), ("p", r.p), ("P", P),
             ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("tpt", inst), ("hacc", hacc),
             ("hsplit", r.pf), ("!h", h)]
        let _ := p
        return ⟨ehyps, hyps, filled, k⟩
    restoreState saved
  throwIPMError "could not find a points-to in context covering the address {l}"

/-- One `wp_store` step: find `GoStore t (#l, #w)` and a spatial hypothesis
`P` with `Access (l ↦ v) (l ↦ w) P P'`; `P` is replaced by `P'` (same name). -/
def iWpStoreStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let some ((t, l, W, w), K, _) ← findEctx wp.e (fun _ e => do
      let some (i, arg) ← isGoInstrApp? e ``go_instruction.GoStore | throwError "no"
      let arg ← whnfR arg
      let_expr Perennial.val.PairV _ lv wv := arg | throwError "no"
      let some (_, l) ← isIntoVal? lv | throwError "no"
      let some (W, w) ← isIntoVal? wv | throwError "no"
      return (i.getArg! 1, l, W, w))
    | throwIPMError "could not find a store `GoStore t (#l, #w)`"
  let GF := (← gooseGSArgs wp.ι)[6]!
  let own1 ← mkAppM ``DFrac.own #[← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Iris.Qp), some (mkRawNatLit 1), none]]
  for (name, ivar, p, P) in hypsList hyps do
    if isTrue p then continue
    let saved ← saveState
    let (A, _, inst, v, _) ← mkTypedPointstoMVars GF l (some W) none (some own1)
    let A' ← mkAppOptM ``typed_pointsto #[some GF, some W, some inst, some l, some w, some own1]
    if let some (hacc, P') ← synthAccess A A' P then
      let r := hyps.remove true ivar
      let ⟨_, hyps'', hadd⟩ := r.hyps'.add bi name ivar q(false) P'
      let unitV ← mkAppOptM ``GoGlobalContext.into_val #[none, none, some (mkConst ``Unit), some (mkConst ``Unit.unit)]
      let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.expr.Val) wp.ext unitV)
      let k := fun (h : Expr) => do
        mkAppNamed ``tac_wp_store
          [("V", W), ("t", t), ("K", wp.quoteK K), ("l", l), ("v", ← instantiateMVars v),
           ("w", w), ("Δ", ehyps), ("P", P), ("P'", P'),
           ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("tpt", ← instantiateMVars inst),
           ("hacc", hacc), ("hsplit", r.pf), ("hadd", hadd), ("!h", h)]
      return ⟨_, hyps'', filled, k⟩
    restoreState saved
  throwIPMError "could not find a points-to in context covering the address {l}"

/-- A `wp_alloc` step: find `GoAlloc t #v` (optionally only as the argument of
`let: "x" := _ in _`, when `auto`), and continue under a fresh location `l`
with the new hypothesis `l ↦ v`. `names` gives the Lean and Iris names (from
the `let:` binder when `auto`: `x_ptr` and `x`). -/
def iWpAllocStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (auto : Bool)
    (names : Option (Name × Name))
    (k : ∀ {ehyps' : Q($prop)}, Hyps bi ehyps' → GooseWpGoal → ProofModeM Expr) :
    ProofModeM Expr := do
  let some ((t, V, v, letName?), K, _) ← findEctx wp.e (fun K e => do
      let some (i, vv) ← isGoInstrApp? e ``go_instruction.GoAlloc | throwError "no"
      let some (V, v) ← isIntoVal? vv | throwError "no"
      -- the `let:` binder name, from the enclosing evaluation context item
      let letName? ← match K with
        | Ki :: _ =>
          let Ki ← whnfR Ki
          if Ki.isAppOfArity ``ectx_item.AppRCtx 2 then
            let f ← whnfR (Ki.getArg! 1)
            match_expr f with
            | Perennial.expr.Rec _ fb xb _ =>
              let fb ← whnfR fb; let xb ← whnfR xb
              if fb.isAppOf ``binder.BAnon then
                match_expr xb with
                | binder.BNamed s =>
                  match (← whnfR s) with
                  | .lit (.strVal s) => pure (some s)
                  | _ => pure none
                | _ => pure none
              else pure none
            | _ => pure none
          else pure none
        | [] => pure none
      if auto && letName?.isNone then throwError "no"
      return (i.getArg! 1, V, v, letName?))
    | throwIPMError "could not find an allocation `GoAlloc t #v`"
  let (lName, hName) := match names, letName? with
    | some ns, _ => ns
    | none, some x => (Name.mkSimple (x ++ "_ptr"), Name.mkSimple x)
    | none, none => (`l, `Hl)
  let GF := (← gooseGSArgs wp.ι)[6]!
  let own1 ← mkAppM ``DFrac.own #[← mkAppOptM ``OfNat.ofNat #[some (mkConst ``Iris.Qp), some (mkRawNatLit 1), none]]
  let instTy ← mkAppOptM ``TypedPointsto #[some GF, some V]
  let inst ← synthInstance instTy
  let locTy := mkConst ``Perennial.loc
  let pf ← withLocalDeclD lName locTy fun l => do
    let pt ← mkAppOptM ``typed_pointsto #[some GF, some V, some inst, some l, some v, some own1]
    let ivar ← mkFreshIVarId false
    let ⟨_, hyps', hadd⟩ := hyps.add bi hName ivar q(false) pt
    let lv ← mkAppOptM ``GoGlobalContext.into_val #[none, none, some locTy, some l]
    let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.expr.Val) wp.ext lv)
    let pfCont ← k hyps' { wp with e := filled }
    -- `hadd : Δ ∗ □?false (l ↦ v) ⊣⊢ Δ'`
    let pfl ← mkAppNamed ``tac_add_hyp
      [("Δ", ehyps), ("P", pt), ("hadd", hadd), ("Q", wp.mk' filled wp.Φ), ("!h", pfCont)]
    mkLambdaFVars #[l] pfl
  mkAppNamed ``tac_wp_alloc
    [("V", V), ("t", t), ("K", wp.quoteK K), ("v", v), ("Δ", ehyps),
     ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("tpt", inst), ("!h", pf)]

end tactics

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_load` performs a typed load `![t] #l` in evaluation position, using a
hypothesis covering `l`: either `l ↦{dq} v` itself, or a hypothesis from which
it can be accessed (`Access` instance, e.g. a struct points-to for a field
address). The load produces `#v`. -/
elab "wp_load" : tactic =>
  runTacticGooseWp `wp_load fun mvar g wp => do
    let ⟨_, hyps', e', k⟩ ← iWpLoadStep g.hyps wp
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_store` performs a typed store `GoStore t (#l, #w)` in evaluation
position, using a spatial hypothesis covering `l` with full ownership, which is
updated to the new value. -/
elab "wp_store" : tactic =>
  runTacticGooseWp `wp_store fun mvar g wp => do
    let ⟨_, hyps', e', k⟩ ← iWpStoreStep g.hyps wp
    mvar.assign (← k (← iWpFinish hyps' { wp with e := e' }))

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc l as H` performs an allocation `GoAlloc t #v` in evaluation
position, introducing the location `l` and the hypothesis `H : l ↦ v`. -/
elab "wp_alloc " l:ident " as " H:ident : tactic =>
  runTacticGooseWp `wp_alloc fun mvar g wp => do
    mvar.assign (← iWpAllocStep g.hyps wp false (some (l.getId, H.getId))
      fun hyps' wp' => iWpFinish hyps' wp')

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_alloc_auto` performs an allocation `let: "x" := GoAlloc t #v in e`,
naming the location `x_ptr` and the points-to `x`. -/
elab "wp_alloc_auto" : tactic =>
  runTacticGooseWp `wp_alloc_auto fun mvar g wp => do
    mvar.assign (← iWpAllocStep g.hyps wp true none fun hyps' wp' => iWpFinish hyps' wp')

end Perennial
