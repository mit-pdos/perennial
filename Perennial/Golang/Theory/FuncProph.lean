module

public import Perennial.Golang.Theory.WithProph
public import Perennial.Golang.Defn
public import Perennial.GooseLang.FuncInstrument

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## Transferring a structure along definitional equalities of its fields -/

open Lean Meta Elab Tactic in
/-- `transferTerm T h` (with `h : T'`): a term of type `T` built from `h`, where `T` and `T'`
differ only in ways that are definitional in the fields: `h` itself if the types are
definitionally equal; under binders, the transfer of the body (the binder's value transferred
back); for a structure, its constructor applied to the transfers of `h`'s fields. What is left
is returned as goals of type `T' → T` (for the corresponding piece of `h`). -/
meta partial def transferTerm (lemmas : Array Lean.Expr) (lctx : LocalContext) (linst : LocalInstances)
    (xs : Array Lean.Expr) (T : Lean.Expr) (h : Lean.Expr) :
    MetaM (Lean.Expr × Array MVarId) := do
  let T' ← inferType h
  if ← withDefault (isDefEq T T') then return (h, #[])
  let Tw ← whnf T
  let T'w ← whnf T'
  match Tw, T'w with
  | .forallE n A B bi, .forallE _ A' _ _ =>
    withLocalDecl n bi A fun x => do
      let (x', gs1) ← transferTerm lemmas lctx linst (xs.push x) A' x
      let (b, gs2) ← transferTerm lemmas lctx linst (xs.push x) (B.instantiate1 x) (mkApp h x')
      return (← mkLambdaFVars #[x] b, gs1 ++ gs2)
  | _, _ =>
    let leftover : MetaM (Lean.Expr × Array MVarId) := do
      let ty ← mkForallFVars xs (← mkArrow T' T)
      let m ← mkFreshExprMVarAt lctx linst ty
      return (mkApp (mkAppN m xs) h, #[m.mvarId!])
    for l in lemmas do
      let r ← observing? do
        let (mvs, _, concl) ← forallMetaTelescopeReducing (← inferType l)
        unless ← withDefault (isDefEq concl Tw) do throwError "no"
        let v ← instantiateMVars (mkAppN l mvs)
        if v.hasExprMVar then throwError "no"
        return v
      if let some v := r then return (v, #[])
    if (← isClass? Tw).isSome then
      if let some inst ← observing? (synthInstance Tw) then return (inst, #[])
    let .const sName us := Tw.getAppFn | leftover
    let .const sName' _ := T'w.getAppFn | leftover
    let env ← getEnv
    unless sName == sName' && isStructure env sName do return ← leftover
    let ctor := getStructureCtor env sName
    let params := Tw.getAppArgs[:ctor.numParams].toArray
    let mut app := mkAppN (mkConst ctor.name us) params
    let mut gs : Array MVarId := #[]
    for i in [:ctor.numFields] do
      let fTy ← whnf (← inferType app)
      let .forallE _ A _ _ := fTy | throwError "transferTerm: bad constructor type"
      let (v, gs') ← transferTerm lemmas lctx linst xs A (mkProj sName i h)
      gs := gs ++ gs'
      app := mkApp app v
    return (app, gs)

open Lean Meta Elab Tactic in
/-- `transfer h using l₁, …`: close the goal from `h` by `transferTerm`, also trying the lemmas
`lᵢ` (whose conclusions are unified with the pieces); the pieces that do not transfer
definitionally are left as goals `T' → T`. -/
meta def transferTac (h : Syntax) (ls : Array Syntax) : TacticM Unit := withMainContext do
  let g ← getMainGoal
  let hv ← instantiateMVars (← Term.withSynthesize (elabTerm h none))
  let mut lemmas := #[]
  for l in ls do
    lemmas := lemmas.push (← instantiateMVars (← Term.withSynthesize (elabTerm l none)))
  let (v, gs) ← transferTerm lemmas (← getLCtx) (← getLocalInstances) #[] (← g.getType) hv
  g.assign v
  replaceMainGoal gs.toList

elab "transfer " h:term " using " ls:term,+ : tactic => transferTac h ls.getElems
elab "transfer " h:term : tactic => transferTac h #[]

section model
variable [GooseExts] [GoGlobalContext]

open Classical in
def patchFns (S : GoSemanticsFunctions) (f : GoString) (w : GoFunc) : GoSemanticsFunctions :=
  { S with functions := fun n ts => match ts with
      | [] => if n = f then w else S.functions n []
      | ts => S.functions n ts }

/-- The functions without type arguments whose bodies the Go semantics itself states
(`go.Semantics`'s `FuncUnfold` facts): a function patched by `patchFns` must not be one. -/
def reservedFuncs : List GoString :=
  [go.panic, github_com.mit_pdos.perennial.goose.model.channel.runtimePanic,
    github_com.goose_lang.primitive.RandomUint64, github_com.goose_lang.primitive.Assume,
    github_com.goose_lang.primitive.NewProph,
    github_com.mit_pdos.perennial.goose.model.strings.StringToByteSlice,
    github_com.mit_pdos.perennial.goose.model.strings.ByteSliceToString,
    github_com.mit_pdos.perennial.goose.model.strings.DecodeRune,
    github_com.mit_pdos.perennial.goose.model.strings.decoderune, go.min, go.max]

section patch
variable (F : GoInstruction → val → Expr → Prop) (sem : @go.Semantics _ ⟨F⟩ _) (f : GoString)
  (w : GoFunc)

theorem patchFns_functions_nil (n : GoString) :
    @functions _ (patchFns sem.sem_fn f w) n [] = if n = f then w else @functions _ sem.sem_fn n [] :=
  rfl

theorem patchFns_functions_ne (n : GoString) (ts : List go.GoType) (hn : n ≠ f) :
    @functions _ (patchFns sem.sem_fn f w) n ts = @functions _ sem.sem_fn n ts := by
  cases ts
  · rw [patchFns_functions_nil, if_neg hn]
  · rfl

theorem patch_func_resolve (n : GoString) (ts : List go.GoType) :
    @go.IsGoStepPureDet _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ (FuncResolve n ts) #()
      (Val (#(@functions _ (patchFns sem.sem_fn f w) n ts) : val)) := by
  have h0 := @go.CoreSemantics.go_func_resolve_step _ ⟨F⟩ _ sem.sem_fn
    (@go.PreSemantics.core_sem _ ⟨F⟩ _ sem.sem_fn (@go.Semantics.core_sem _ ⟨F⟩ _ sem)) n ts
  refine @go.IsGoStepPureDet.mk _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ _ _ _ (fun _ _ _ => Iff.rfl) ?_
  have h1 := h0.2
  have hc := @go.PreSemantics.core_sem _ ⟨F⟩ _ sem.sem_fn (@go.Semantics.core_sem _ ⟨F⟩ _ sem)
  have hunit : (#() : val) = unitV := congrFun hc.intoVal_unfold_unit.intoVal_unfold ()
  have hfunc : (#w : val) = RecV w.f w.x w.e := congrFun hc.intoVal_unfold_func.intoVal_unfold w
  cases ts with
  | nil =>
    by_cases hn : n = f
    · subst hn; funext e
      rw [patchLctx_nil, patchFns_functions_nil, if_pos rfl, if_pos ⟨rfl, hunit⟩, hfunc]
      exact propext ⟨Eq.symm, Eq.symm⟩
    · funext e
      have := congrFun h1 e
      rw [patchLctx_nil, patchFns_functions_nil, if_neg (fun h => hn h.1), if_neg hn]
      exact this
  | cons t ts => exact h1

theorem TCForall_imp {A : Type} {P Q : A → Prop} {l : List A} (h : TCForall P l)
    (hpq : ∀ a, P a → Q a) : TCForall Q l := by
  induction h with
  | nil => exact .nil
  | @cons a l ha _ ih => exact @TCForall.cons _ _ a l (hpq a ha) ih

theorem PlainLayout_congr {S S' : GoSemanticsFunctions}
    (hu : ∀ t, @underlying _ S t = @underlying _ S' t) {t : go.GoType} {s a : Nat}
    (h : @go.PlainLayout _ S t s a) : @go.PlainLayout _ S' t s a := by
  refine @go.PlainLayout.rec _ S (fun t s a _ => @go.PlainLayout _ S' t s a)
    (fun fds off stop al _ => @go.PlainFields _ S' fds off stop al) ?_ ?_ ?_ ?_ ?_ ?_ t s a h
  · intro t w h; exact .scalar t w h
  · intro n e s a _ h1 ih; exact .array n e s a ih h1
  · intro fds s a h1 _ h3 ih; exact .struct fds s a h1 ih h3
  · intro t u s a h1 h2 _ ih; exact .named t u s a ((hu t).symm.trans h1) h2 ih
  · intro off; exact .nil off
  · intro fd fds off s a stop a' _ h2 h3 _ ih1 ih2; exact .cons fd fds off s a stop a' ih1 h2 h3 ih2

theorem PlainFieldOffset_congr {S S' : GoSemanticsFunctions}
    (hu : ∀ t, @underlying _ S t = @underlying _ S' t) {fds : List go.field_decl} {base : Nat}
    {g : GoString} {off : Nat}
    (h : @go.PlainFieldOffset _ S fds base g off) : @go.PlainFieldOffset _ S' fds base g off := by
  induction h with
  | here fd fds base => exact .here fd fds base
  | there fd fds base s a g off h1 h2 _ ih => exact .there fd fds base s a g off h1 (PlainLayout_congr hu h2) ih

variable (hf : f ∉ reservedFuncs)
include hf

theorem not_reserved {n : GoString} (hn : n ∈ reservedFuncs) : n ≠ f := by
  intro heq; subst heq; exact hf hn

/-- Closes the goals `transfer` leaves. -/
local macro "close_left" : tactic => `(tactic| first
  | (intros; refine PlainLayout_congr ?_ ‹_›; intro; rfl)
  | (intros; refine PlainFieldOffset_congr ?_ ‹_›; intro; rfl)
  | (intro _ _ _ ⟨a, h⟩; refine ⟨a, PlainLayout_congr ?_ h⟩; intro; rfl)
  | (intros; rename_i h; exact TCForall_imp h (fun a ha => by transfer ha))
  | (intros; rename_i h
     simp (disch := exact not_reserved f hf (by simp [reservedFuncs])) only
       [patchFns_functions_ne]
     exact h))

set_option maxHeartbeats 4000000 in
theorem patch_pre : @go.PreSemantics _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ (patchFns sem.sem_fn f w) := by
  transfer sem.core_sem using patch_func_resolve F sem f w
  all_goals close_left

theorem patch_chan : @go.ChanSemantics _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ (patchFns sem.sem_fn f w) := by
  transfer sem.chan_sem
  all_goals close_left

theorem patch_string :
    @go.StringSemantics _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ (patchFns sem.sem_fn f w) := by
  transfer sem.string_sem
  all_goals close_left

theorem patch_pool : @github_com.mit_pdos.perennial.goose.model.pool.Assumptions _ _
    (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) (patchFns sem.sem_fn f w) := by
  transfer sem.pool_sem
  all_goals close_left

/-- **The patched model**: the Go semantics `F` (with its functions `sem.sem_fn`) with the
function `f` (no type arguments) resolved to `w` instead, satisfies the Go semantics. -/
def patchSem : @go.Semantics _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ :=
  @go.Semantics.mk _ (patchLctx ⟨F⟩ f (RecV w.f w.x w.e)) _ (patchFns sem.sem_fn f w)
    (patch_pre F sem f w hf) (patch_chan F sem f w hf) (patch_string F sem f w hf)
    (patch_pool F sem f w hf)

end patch

end model
end Perennial
