/-
Prophecy instrumentation of one function, proved sound (nothing trusted).

A proof may run the function `f` (no type arguments, two arguments) as its instrumented body
`prophFnV impl`: the original body `impl` under a prophecy of its result (`withProph`), so that
`f`'s own spec can use a prophecy that its callers never see. The instrumented program is the
same program in a patched Go model, `patchLctx L f (prophFnV impl)`, in which `FuncResolve f []`
resolves to the instrumented body; `goose_adequacy_funcProph` concludes, from a WP in the
patched model, `goose_adequacy`'s conclusions about the real executions in the model `L`.

The simulation: a real execution is matched by an instrumented one whose threads are the real
ones with the wrapper's frames `prophCtx #p` inserted around the running calls of `f`
(`ThreadRel`), in the same state but for the patched model and the instrumentation's prophecy
ids. A call of `f` takes, in the instrumented program, the wrapper's extra plain steps (the
prophecy's creation; at the return, its resolution), which use no fuel.

This needs the call of `f` to be what is resolved: the instruction value `GoInstruction
(FuncResolve f [])` must be applied to its unit argument and to two arguments as soon as it is
evaluated, never stored, compared or passed to another instruction, since the real and the
instrumented executions resolve it to different closures. `ok` is that condition on the
program's code, decidable and checked; it holds of the whole configuration along the execution
given the same of the Go model's instruction results (`GoodModel`) and the extensions' steps
(`GoodExts`): conditions on what the model and the extensions may return, not on the program.
-/
module

public import Perennial.GooseLang.ProphInstrument

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Language.Notation

section defs
variable [GooseExts]

/-- The instrumented body of the two-argument function `impl`: `impl` applied to its arguments,
under a prophecy of its result. -/
def prophFnV (impl : val) : val :=
  RecV BAnon "$a1" (Rec BAnon "$a2" (withProph (App (App (Val impl) (Var "$a1")) (Var "$a2"))))

open Classical in
/-- The Go model `L` with `FuncResolve f []` resolving to `w`. -/
def patchLctx (L : GoLocalContext) (f : GoString) (w : val) : GoLocalContext where
  is_go_step_pure op arg e := match op with
    | .FuncResolve n [] =>
      if n = f ∧ arg = unitV then e = Val w else L.is_go_step_pure (.FuncResolve n []) arg e
    | op => L.is_go_step_pure op arg e

theorem patchLctx_nil (L : GoLocalContext) (f : GoString) (v : val) (n : GoString) (a : val)
    (e : Expr) :
    @GoLocalContext.is_go_step_pure _ (patchLctx L f v) (.FuncResolve n []) a e =
      if n = f ∧ a = unitV then e = Val v else L.is_go_step_pure (.FuncResolve n []) a e := rfl

theorem patchLctx_other (L : GoLocalContext) (f : GoString) (v : val) (op : GoInstruction)
    (a : val) (h : ¬ (op = .FuncResolve f [] ∧ a = unitV)) :
    @GoLocalContext.is_go_step_pure _ (patchLctx L f v) op a =
      L.is_go_step_pure op a := by
  funext e
  cases op <;> try rfl
  rename_i n ts
  cases ts with
  | nil =>
    rw [patchLctx_nil, if_neg]
    rintro ⟨rfl, rfl⟩; exact h ⟨rfl, rfl⟩
  | cons => rfl

/-! ## Calls in position

`ok gi n e`: in `e`, the value `gi` occurs only where it is applied to three arguments (its unit
argument and the function's two), `n` being the number of arguments the position of `e`
receives (`App e₁ e₂` passes one more to `e₁`'s position). `okV gi v`: `v` is not `gi` and
holds no `gi` but in such positions. -/

mutual
def ok (gi : val) (n : Nat) : Expr → Prop
  | Val v => (v = gi ∧ 3 ≤ n) ∨ okV gi v
  | Var _ => True
  | Rec _ _ e => ok gi 0 e
  | App e1 e2 => ok gi (n + 1) e1 ∧ ok gi 0 e2
  | If e0 e1 e2 => ok gi 0 e0 ∧ ok gi 0 e1 ∧ ok gi 0 e2
  | Pair e1 e2 => ok gi 0 e1 ∧ ok gi 0 e2
  | Fst e => ok gi 0 e
  | Snd e => ok gi 0 e
  | Fork e => ok gi 0 e
  | Primitive0 _ => True
  | Primitive1 _ e => ok gi 0 e
  | Primitive2 _ e1 e2 => ok gi 0 e1 ∧ ok gi 0 e2
  | CmpXchg e0 e1 e2 => ok gi 0 e0 ∧ ok gi 0 e1 ∧ ok gi 0 e2
  | ExternalOp _ _ e => ok gi 0 e
  | NewProph => True
  | ResolveProph e1 e2 => ok gi 0 e1 ∧ ok gi 0 e2
  | LiteralValue l => okKEs gi l
  | SelectStmtClauses d l => okOpt gi d ∧ okCCs gi l
  | Catch e h k => ok gi 0 e ∧ ok gi 0 h ∧ ok gi 0 k

def okV (gi : val) : val → Prop
  | LitV _ => True
  | RecV _ _ e => ok gi 0 e
  | PairV v1 v2 => okV gi v1 ∧ okV gi v2
  | InjLV v => okV gi v
  | InjRV v => okV gi v
  | ExtV _ => True
  | .GoInstruction o => val.GoInstruction o ≠ gi
  | ArrayV vs => okVs gi vs
  | InterfaceV t => okIface gi t
  | LiteralValueV l => okKEs gi l
  | SelectStmtClausesV d l => okOpt gi d ∧ okCCs gi l
  | UntypedNil => True
  | PanicV p => okV gi p

def okVs (gi : val) : List val → Prop
  | [] => True
  | v :: vs => okV gi v ∧ okVs gi vs

def okIface (gi : val) : Option (go.GoType × val) → Prop
  | none => True
  | some (_, v) => okV gi v

def okOpt (gi : val) : Option Expr → Prop
  | none => True
  | some e => ok gi 0 e

def okKEs (gi : val) : List keyed_element → Prop
  | [] => True
  | ke :: l => okKE gi ke ∧ okKEs gi l

def okKE (gi : val) : keyed_element → Prop
  | .KeyedElement k el => okOptKey gi k ∧ okElement gi el

def okOptKey (gi : val) : Option key → Prop
  | none => True
  | some (.KeyExpression _ e) => ok gi 0 e
  | some (.KeyLiteralValue l) => okKEs gi l
  | some _ => True

def okElement (gi : val) : Element → Prop
  | .ElementExpression _ e => ok gi 0 e
  | .ElementLiteralValue l => okKEs gi l

def okCCs (gi : val) : List comm_clause → Prop
  | [] => True
  | c :: l => okCC gi c ∧ okCCs gi l

def okCC (gi : val) : comm_clause → Prop
  | .CommClause (.SendCase _ b e) body => ok gi 0 b ∧ ok gi 0 e ∧ ok gi 0 body
  | .CommClause (.RecvCase _ e) body => ok gi 0 e ∧ ok gi 0 body
end

end defs

section okLemmas
variable [GooseExts] {gi : val}

theorem ok_val0 (v : val) : ok gi 0 (Val v) ↔ okV gi v := by
  simp [ok]

theorem ok_val (n : Nat) {v : val} (h : okV gi v) : ok gi n (Val v) := by
  simp [ok, h]

theorem ok_mono : ∀ {n m : Nat} {e : Expr}, n ≤ m → ok gi n e → ok gi m e
  | n, m, Val v, h, H => by
    simp only [ok] at H ⊢
    rcases H with ⟨h1, h2⟩ | H
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr H
  | n, m, App e1 e2, h, H => by
    simp only [ok] at H ⊢
    exact ⟨ok_mono (by omega) H.1, H.2⟩
  | _, _, Var _, _, H => H
  | _, _, Rec .., _, H => H
  | _, _, If .., _, H => H
  | _, _, Pair .., _, H => H
  | _, _, Fst .., _, H => H
  | _, _, Snd .., _, H => H
  | _, _, Fork .., _, H => H
  | _, _, Primitive0 .., _, H => H
  | _, _, Primitive1 .., _, H => H
  | _, _, Primitive2 .., _, H => H
  | _, _, CmpXchg .., _, H => H
  | _, _, ExternalOp .., _, H => H
  | _, _, NewProph, _, H => H
  | _, _, ResolveProph .., _, H => H
  | _, _, LiteralValue .., _, H => H
  | _, _, SelectStmtClauses .., _, H => H
  | _, _, Catch .., _, H => H

theorem ok_of_ok0 {n : Nat} {e : Expr} (h : ok gi 0 e) : ok gi n e := ok_mono (Nat.zero_le _) h

mutual
theorem ok_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (n : Nat) (e : Expr), ok gi n e → ok gi n (subst x v e)
  | n, Val _, H => H
  | n, Var y, H => by
    simp only [subst]; split
    · exact ok_val n hv
    · exact H
  | n, Rec f y e, H => by
    simp only [subst, ok] at H ⊢; split
    · exact ok_subst x v hv 0 e H
    · exact H
  | n, App e1 e2, H => ⟨ok_subst x v hv _ e1 H.1, ok_subst x v hv _ e2 H.2⟩
  | n, If e0 e1 e2, H =>
    ⟨ok_subst x v hv _ e0 H.1, ok_subst x v hv _ e1 H.2.1, ok_subst x v hv _ e2 H.2.2⟩
  | n, Pair e1 e2, H => ⟨ok_subst x v hv _ e1 H.1, ok_subst x v hv _ e2 H.2⟩
  | n, Fst e, H => ok_subst x v hv _ e H
  | n, Snd e, H => ok_subst x v hv _ e H
  | n, Fork e, H => ok_subst x v hv _ e H
  | n, Primitive0 _, H => H
  | n, Primitive1 _ e, H => ok_subst x v hv _ e H
  | n, Primitive2 _ e1 e2, H => ⟨ok_subst x v hv _ e1 H.1, ok_subst x v hv _ e2 H.2⟩
  | n, CmpXchg e0 e1 e2, H =>
    ⟨ok_subst x v hv _ e0 H.1, ok_subst x v hv _ e1 H.2.1, ok_subst x v hv _ e2 H.2.2⟩
  | n, ExternalOp _ _ e, H => ok_subst x v hv _ e H
  | n, NewProph, H => H
  | n, ResolveProph e1 e2, H => ⟨ok_subst x v hv _ e1 H.1, ok_subst x v hv _ e2 H.2⟩
  | n, LiteralValue l, H => okKEs_subst x v hv l H
  | n, SelectStmtClauses d l, H => ⟨okOpt_subst x v hv d H.1, okCCs_subst x v hv l H.2⟩
  | n, Catch e h k, H =>
    ⟨ok_subst x v hv _ e H.1, ok_subst x v hv _ h H.2.1, ok_subst x v hv _ k H.2.2⟩

theorem okOpt_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (d : Option Expr), okOpt gi d → okOpt gi (substOpt x v d)
  | none, H => H
  | some e, H => ok_subst x v hv 0 e H

theorem okKEs_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (l : List keyed_element), okKEs gi l → okKEs gi (substKeyedElements x v l)
  | [], H => H
  | ke :: l, H => ⟨okKE_subst x v hv ke H.1, okKEs_subst x v hv l H.2⟩

theorem okKE_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (ke : keyed_element), okKE gi ke → okKE gi (substKeyedElement x v ke)
  | .KeyedElement k el, H => ⟨okOptKey_subst x v hv k H.1, okElement_subst x v hv el H.2⟩

theorem okOptKey_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (k : Option key), okOptKey gi k → okOptKey gi (substOptKey x v k)
  | none, H => H
  | some (.KeyExpression _ e), H => ok_subst x v hv 0 e H
  | some (.KeyLiteralValue l), H => okKEs_subst x v hv l H
  | some (.KeyField _), H => H
  | some (.KeyInteger _), H => H

theorem okElement_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (el : Element), okElement gi el → okElement gi (substElement x v el)
  | .ElementExpression _ e, H => ok_subst x v hv 0 e H
  | .ElementLiteralValue l, H => okKEs_subst x v hv l H

theorem okCCs_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (l : List comm_clause), okCCs gi l → okCCs gi (substCommClauses x v l)
  | [], H => H
  | c :: l, H => ⟨okCC_subst x v hv c H.1, okCCs_subst x v hv l H.2⟩

theorem okCC_subst (x : String) (v : val) (hv : okV gi v) :
    ∀ (c : comm_clause), okCC gi c → okCC gi (substCommClause x v c)
  | .CommClause (.SendCase _ b e) body, H =>
    ⟨ok_subst x v hv 0 b H.1, ok_subst x v hv 0 e H.2.1, ok_subst x v hv 0 body H.2.2⟩
  | .CommClause (.RecvCase _ e) body, H => ⟨ok_subst x v hv 0 e H.1, ok_subst x v hv 0 body H.2⟩
end

theorem ok_subst' (x : Binder) (v : val) (hv : okV gi v) (n : Nat) (e : Expr) (H : ok gi n e) :
    ok gi n (subst' x v e) := by
  cases x with
  | BAnon => exact H
  | BNamed x => exact ok_subst x v hv n e H

/-! ### Evaluation contexts -/

/-- The number of arguments the hole of `Ki` receives, `n` those of `Ki`'s position. -/
def itemLvl (n : Nat) : EctxItem → Nat
  | .AppLCtx .. => n + 1
  | _ => 0

/-- The rest of the frame `Ki`, in a position receiving `n` arguments. -/
def okItem (gi : val) (n : Nat) : EctxItem → Prop
  | .AppLCtx v2 _ => okV gi v2
  | .AppRCtx e1 => ok gi (n + 1) e1
  | .IfCtx e1 e2 => ok gi 0 e1 ∧ ok gi 0 e2
  | .PairLCtx e2 => ok gi 0 e2
  | .PairRCtx v1 _ => okV gi v1
  | .FstCtx => True
  | .SndCtx => True
  | .Primitive1Ctx _ => True
  | .Primitive2LCtx _ e2 => ok gi 0 e2
  | .Primitive2RCtx _ v1 _ => okV gi v1
  | .ExternalOpCtx .. => True
  | .CmpXchgLCtx e1 e2 => ok gi 0 e1 ∧ ok gi 0 e2
  | .CmpXchgMCtx v1 e2 _ => okV gi v1 ∧ ok gi 0 e2
  | .CmpXchgRCtx v1 v2 _ _ => okV gi v1 ∧ okV gi v2
  | .ResolveProphLCtx v2 _ => okV gi v2
  | .ResolveProphRCtx e1 => ok gi 0 e1
  | .CatchCtx h k => ok gi 0 h ∧ ok gi 0 k

theorem ok_fillItem (n : Nat) (Ki : EctxItem) (e : Expr) :
    ok gi n (fillItem Ki e) ↔ okItem gi n Ki ∧ ok gi (itemLvl n Ki) e := by
  cases Ki <;> simp [fillItem, ok, okItem, itemLvl, and_comm, and_left_comm, and_assoc]

/-- `fill`, as the bounded language's contexts fill (innermost frame first). -/
def fillK (K : List EctxItem) (e : Expr) : Expr := K.foldl (fun x y => fillItem y x) e

@[simp] theorem fillK_nil (e : Expr) : fillK [] e = e := rfl
@[simp] theorem fillK_cons (Ki : EctxItem) (K : List EctxItem) (e : Expr) :
    fillK (Ki :: K) e = fillK K (fillItem Ki e) := rfl
theorem fillK_append (K1 K2 : List EctxItem) (e : Expr) :
    fillK (K1 ++ K2) e = fillK K2 (fillK K1 e) := by
  simp [fillK, List.foldl_append]

def ctxLvl (n : Nat) : List EctxItem → Nat
  | [] => n
  | Ki :: K => itemLvl (ctxLvl n K) Ki

def okCtx (gi : val) (n : Nat) : List EctxItem → Prop
  | [] => True
  | Ki :: K => okCtx gi n K ∧ okItem gi (ctxLvl n K) Ki

theorem ok_fillK (n : Nat) (K : List EctxItem) (e : Expr) :
    ok gi n (fillK K e) ↔ okCtx gi n K ∧ ok gi (ctxLvl n K) e := by
  induction K generalizing e with
  | nil => simp [okCtx, ctxLvl]
  | cons Ki K ih =>
    rw [fillK_cons, ih, ok_fillItem]
    simp only [okCtx, ctxLvl, and_assoc]

/-- A call's context: where `gi #()` is evaluated, the next two frames apply it to the
function's arguments. -/
theorem ctx_of_ok_call {o : GoInstruction} {K : List EctxItem} {a : val}
    (h : ok (.GoInstruction o) 0 (fillK K (App (Val (.GoInstruction o)) (Val a)))) :
    ∃ v1 h1 v2 h2 K', K = .AppLCtx v1 h1 :: .AppLCtx v2 h2 :: K' := by
  rw [ok_fillK] at h
  obtain ⟨_, h⟩ := h
  have hl : 2 ≤ ctxLvl 0 K := by
    simp only [ok] at h
    rcases h.1 with ⟨_, h3⟩ | h3
    · omega
    · simp [okV] at h3
  rcases K with _ | ⟨Ki, K⟩
  · simp [ctxLvl] at hl
  cases Ki with
  | AppLCtx v1 h1 =>
    rcases K with _ | ⟨Kj, K'⟩
    · simp [ctxLvl, itemLvl] at hl
    cases Kj with
    | AppLCtx v2 h2 => exact ⟨v1, h1, v2, h2, K', rfl⟩
    | _ => simp [ctxLvl, itemLvl] at hl
  | _ => simp [ctxLvl, itemLvl] at hl

end okLemmas

/-! ### The invariant along an execution -/

section okSteps
variable [GooseExts] [GooseSemantics] [GoGlobalContext] {gi : val}

/-- Every value of the heap is `okV`. -/
def heapOk (gi : val) (h : GMap Loc (NonAtomic val)) : Prop :=
  ∀ l na, h !! l = some na → okV gi na.2

/-- The Go model `L` returns calls in position from arguments without `gi`. -/
def GoodModel (gi : val) (L : GoLocalContext) : Prop :=
  ∀ op a e, L.is_go_step_pure op a e → okV gi a → ok gi 0 e

/-- The extensions' steps keep `gi` in position. -/
def GoodExts (gi : val) : Prop :=
  ∀ ext op v (σg : CfgState) e' (σg' : CfgState), extStep ext op v σg e' σg' → okV gi v →
    heapOk gi σg.1.heap → ok gi 0 e' ∧ heapOk gi σg'.1.heap

theorem heapOk_insert {h : GMap Loc (NonAtomic val)} (hh : heapOk gi h) (l : Loc)
    (na : NonAtomic val) (hv : okV gi na.2) : heapOk gi (<[l := na]> h) := by
  intro l' na' hl'
  rw [lookup_insert_Some] at hl'
  rcases hl' with ⟨_, rfl⟩ | ⟨_, hl'⟩
  · exact hv
  · exact hh l' na' hl'

theorem heapOk_setBytes : ∀ {h : GMap Loc (NonAtomic val)} (l : Loc) (bs : List w8),
    heapOk gi h → heapOk gi (setBytes l bs h)
  | _, _, [], hh => hh
  | _, l, b :: bs, hh => heapOk_setBytes (l +ₗ 1) bs (heapOk_insert hh l _ (by simp [Free, okV]))

theorem heapOk_initHeap {h : GMap Loc (NonAtomic val)} (hh : heapOk gi h) (l : Loc) (v : val)
    (hv : okV gi v) : heapOk gi ({[l := Free v]} ∪ h) := by
  intro l' na' hl'
  simp only [GMap.lookup_union, GMap.lookup_singleton_iff] at hl'
  split at hl'
  · simp only [Option.or, Option.some.injEq] at hl'; subst hl'; exact hv
  · simp only [Option.or] at hl'; exact hh l' na' hl'

theorem okV_bytesVal {w : Nat} {bs : List w8} {v : val} (h : bytesVal w bs = some v) :
    okV gi v := by
  unfold bytesVal at h
  split at h
  · split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> first | trivial | simp [okV]
  · cases h

/-- The values of the basic types the base steps return hold no `gi` (the Go semantics states
them as literals, `go.CoreSemantics.intoVal_unfold_*`, but for prophecy ids). -/
structure IntoValOk (gi : val) : Prop where
  loc : ∀ l : Loc, okV gi #l
  bool : ∀ b : Bool, okV gi #b
  unit : okV gi #()
  w64 : ∀ x : w64, okV gi #x
  w32 : ∀ x : w32, okV gi #x
  w16 : ∀ x : w16, okV gi #x
  w8 : ∀ x : w8, okV gi #x
  proph : ∀ p : proph_id, okV gi #p

theorem okV_atomicAdd' (hI : IntoValOk gi) {v1 v2 v : val} (h : atomicAddEval v1 v2 = some v) :
    okV gi v := by
  unfold atomicAddEval at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h
  · exact hI.w64 _
  · exact hI.w32 _
  · exact hI.w16 _
  · exact hI.w8 _

theorem nz3 : (3 ≤ 0) = False := by simp

/-- **A head step keeps calls in position**, given that the model and the extensions do. -/
theorem HeadStep.keeps_ok {e : Expr} {σg : CfgState} {κ : List Observation} {e' : Expr}
    {σg' : CfgState} {efs : List Expr} (h : HeadStep e σg κ e' σg' efs) (n : Nat)
    (he : ok gi n e) (hh : heapOk gi σg.1.heap) (hL : GoodModel gi σg.1.goState.goLctx)
    (hX : GoodExts gi) (hI : IntoValOk gi) (hgi : ∃ o, gi = val.GoInstruction o) :
    ok gi n e' ∧ heapOk gi σg'.1.heap ∧ ∀ ef ∈ efs, ok gi 0 ef := by
  cases h with
  | unwind hu =>
    obtain ⟨Ki, _, rfl⟩ := hu
    rw [ok_fillItem] at he
    simp only [ok] at he ⊢
    refine ⟨Or.inr ?_, hh, by simp⟩
    rcases he.2 with ⟨h1, _⟩ | h1
    · obtain ⟨o, rfl⟩ := hgi; cases h1
    · exact h1
  | base _ hb =>
    cases hb with
    | RecS f x e σg => exact ⟨ok_val n he, hh, by simp⟩
    | PairS v1 v2 σg =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n ⟨he.1, he.2⟩, hh, by simp⟩
    | BetaS f x e1 v2 σg =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      rcases he with ⟨⟨h1, _⟩ | h1, h2⟩
      · obtain ⟨o, rfl⟩ := hgi; cases h1
      refine ⟨ok_of_ok0 ?_, hh, by simp⟩
      exact ok_subst' x v2 h2 0 _ (ok_subst' f _ h1 0 e1 h1)
    | IfTrueS e1 e2 σg => exact ⟨ok_of_ok0 he.2.1, hh, by simp⟩
    | IfFalseS e1 e2 σg => exact ⟨ok_of_ok0 he.2.2, hh, by simp⟩
    | FstS v1 v2 σg => simp only [Perennial.ok, nz3, and_false, false_or, okV] at he; exact ⟨ok_val n he.1, hh, by simp⟩
    | SndS v1 v2 σg => simp only [Perennial.ok, nz3, and_false, false_or, okV] at he; exact ⟨ok_val n he.2, hh, by simp⟩
    | ForkS e σg =>
      refine ⟨ok_val n hI.unit, hh, ?_⟩
      simp only [List.mem_singleton, forall_eq]
      exact ⟨trivial, he⟩
    | ThreadExitS σg => exact ⟨ok_val n hI.unit, hh, by simp⟩
    | ArbitraryIntS x σg => exact ⟨ok_val n (hI.w64 x), hh, by simp⟩
    | AllocS v l σg hl =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n (hI.loc l), heapOk_initHeap hh l v he, by simp⟩
    | AllocOOMS v σg _ => exact ⟨he, hh, by simp⟩
    | StartReadS l m v σg hl =>
      have hv := hh l _ hl
      exact ⟨ok_val n hv, heapOk_insert hh l _ hv, by simp⟩
    | FinishReadS l m v σg hl =>
      have hv := hh l _ hl
      exact ⟨ok_val n hI.unit, heapOk_insert hh l _ hv, by simp⟩
    | LoadS l m v σg hl => exact ⟨ok_val n (hh l _ hl), hh, by simp⟩
    | PrepareWriteS l v σg hl =>
      have hv := hh l _ hl
      exact ⟨ok_val n hI.unit, heapOk_insert hh l _ hv, by simp⟩
    | FinishStoreS l v σg _ =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n hI.unit, heapOk_insert hh l _ he.2, by simp⟩
    | AtomicSwapS l v0 v σg hl =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n (hh l _ hl), heapOk_insert hh l _ he.2, by simp⟩
    | AtomicAddS l v0 v v' σg hl ha =>
      exact ⟨ok_val n (okV_atomicAdd' hI ha), heapOk_insert hh l _ (okV_atomicAdd' hI ha),
        by simp⟩
    | AllocBytesS w v bs l σg _ _ =>
      exact ⟨ok_val n (hI.loc l), heapOk_setBytes l bs hh, by simp⟩
    | AllocBytesOOMS w v bs σg _ _ => exact ⟨he, hh, by simp⟩
    | LoadBytesS w l bs v σg _ hv => exact ⟨ok_val n (okV_bytesVal hv), hh, by simp⟩
    | SwapBytesS w l bs v0 v bs' σg _ hv _ =>
      exact ⟨ok_val n (okV_bytesVal hv), heapOk_setBytes l bs' hh, by simp⟩
    | AddBytesS w l bs v0 v v' bs' σg _ _ ha _ =>
      exact ⟨ok_val n (okV_atomicAdd' hI ha), heapOk_setBytes l bs' hh, by simp⟩
    | CmpXchgBytesFailS w l bs vl v1 v2 σg _ hv _ =>
      exact ⟨ok_val n ⟨okV_bytesVal hv, hI.bool _⟩, hh, by simp⟩
    | CmpXchgBytesSucS w l bs vl v1 v2 bs' σg _ hv _ _ =>
      exact ⟨ok_val n ⟨okV_bytesVal hv, hI.bool _⟩, heapOk_setBytes l bs' hh, by simp⟩
    | ExternalOpS ext op v e' σg σg' hst =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      obtain ⟨h1, h2⟩ := hX ext op v σg e' σg' hst he hh
      exact ⟨ok_of_ok0 h1, h2, by simp⟩
    | GoInstructionS op arg e' s' σg hst =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      refine ⟨?_, hh, by simp⟩
      unfold IsGoStep at hst
      split at hst
      · obtain ⟨-, rfl, -⟩ := hst; exact ok_val n (hI.bool _)
      · obtain ⟨-, rfl, -⟩ := hst; exact ok_val n hI.unit
      · obtain ⟨-, rfl, -⟩ := hst; exact ok_val n hI.unit
      · exact ok_of_ok0 (hL _ _ _ hst.1 he.2)
    | CmpXchgFailS l m vl v1 v2 σg hl _ =>
      exact ⟨ok_val n ⟨hh l _ hl, hI.bool _⟩, hh, by simp⟩
    | CmpXchgSucS l vl v1 v2 σg hl _ =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n ⟨hh l _ hl, hI.bool _⟩, heapOk_insert hh l _ he.2.2, by simp⟩
    | NewProphS p σg _ => exact ⟨ok_val n (hI.proph p), hh, by simp⟩
    | ResolveProphS p w σg => exact ⟨ok_val n hI.unit, hh, by simp⟩
    | LiteralValueS l σg => exact ⟨ok_val n he, hh, by simp⟩
    | SelectStmtClausesS d cs σg => exact ⟨ok_val n he, hh, by simp⟩
    | RaiseS v σg =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨ok_val n he, hh, by simp⟩
    | CatchPanicS q h k σg =>
      simp only [Perennial.ok, nz3, and_false, false_or, okV] at he
      exact ⟨⟨ok_of_ok0 he.2.1, by simpa [ok_val0] using he.1⟩, hh, by simp⟩
    | CatchValS v h k σg _ =>
      simp only [Perennial.ok, nz3, and_false, false_or] at he
      exact ⟨⟨ok_of_ok0 he.2.2, by simpa [ok_val0] using he.1⟩, hh, by simp⟩

end okSteps

/-! ## The instrumented state: the patched model, and the wrapper's prophecy ids -/

section instrState
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- The local state with the Go model `L`. -/
def setLctx (L : GoLocalContext) (σ : state) : state :=
  { σ with goState := { σ.goState with goLctx := L } }

theorem extStep_setLctx (L : GoLocalContext) {ext op : String} {v : val} {σ σ' : state}
    {g g' : GlobalState} {e' : Expr} (h : extStep ext op v (σ, g) e' (σ', g')) :
    extStep ext op v (setLctx L σ, g) e' (setLctx L σ', g') := by
  obtain ⟨E, hE, h', s', gw', hs, heq⟩ := h
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl⟩ := heq
  exact ⟨E, hE, h', s', gw', hs, rfl⟩

theorem extStep_unsetLctx (L : GoLocalContext) {ext op : String} {v : val} {σ : state}
    {g : GlobalState} {e' : Expr} {σg' : CfgState} (h : extStep ext op v (setLctx L σ, g) e' σg') :
    ∃ σg'', extStep ext op v (σ, g) e' σg'' := by
  obtain ⟨E, hE, h', s', gw', hs, -⟩ := h
  exact ⟨_, E, hE, h', s', gw', hs, rfl⟩

theorem IsGoStep_congr {L L' : GoLocalContext} {op : GoInstruction} {a : val}
    (h : @GoLocalContext.is_go_step_pure _ L' op a = @GoLocalContext.is_go_step_pure _ L op a)
    (e' : Expr) (s s' : GMap GoString Bool) :
    @IsGoStep _ _ L' op a e' s s' ↔ @IsGoStep _ _ L op a e' s s' := by
  unfold IsGoStep; split <;> simp [h]

theorem BytesAt_heap {σg σg' : CfgState} (hh : σg.1.heap = σg'.1.heap) {l : Loc} {bs : List w8}
    {r : Bool} (h : BytesAt σg l bs r) : BytesAt σg' l bs r := by
  induction bs generalizing l with
  | nil => trivial
  | cons b bs ih => exact ⟨hh ▸ h.1, ih h.2⟩

/-- A base step in the model `L'`, where `L'` agrees with the state's model on the redex. -/
theorem BaseStep.setLctx (L' : GoLocalContext) {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : BaseStep e (σ, g) κ e' (σ', g') efs)
    (hL : ∀ op a, e = App (Val (.GoInstruction op)) (Val a) →
      @GoLocalContext.is_go_step_pure _ L' op a =
        @GoLocalContext.is_go_step_pure _ σ.goState.goLctx op a) :
    BaseStep e (Perennial.setLctx L' σ, g) κ e' (Perennial.setLctx L' σ', g') efs := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | ExternalOpS ext op v e' σg σg' hst =>
    subst hs hs'
    exact .ExternalOpS _ _ _ _ _ _ (extStep_setLctx L' hst)
  | GoInstructionS op arg e' s' σg hst =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'
    have h2 : @IsGoStep _ _ L' op arg e' σ.goState.packageState s' :=
      (IsGoStep_congr (L := σ.goState.goLctx) (L' := L') (hL op arg rfl) _ _ _).2 hst
    exact BaseStep.GoInstructionS op arg e' s' (Perennial.setLctx L' σ, g') h2
  | _ =>
    subst hs
    simp only [Prod.mk.injEq, setHeap, stateInitHeap] at hs'
    obtain ⟨rfl, rfl⟩ := hs'
    constructor <;> first | assumption | (refine BytesAt_heap ?_ ‹BytesAt _ _ _ _›; rfl)

end instrState

section instrState2
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

theorem setLctx_self (σ : state) : setLctx σ.goState.goLctx σ = σ := by
  obtain ⟨h, ⟨L, ps⟩, w, t⟩ := σ; rfl

theorem setLctx_setLctx (L L' : GoLocalContext) (σ : state) :
    setLctx L (setLctx L' σ) = setLctx L σ := rfl

@[simp] theorem setLctx_goLctx (L : GoLocalContext) (σ : state) :
    (setLctx L σ).goState.goLctx = L := rfl

theorem HeadStep.setLctx (L' : GoLocalContext) {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr}
    (h : HeadStep e (σ, g) κ e' (σ', g') efs)
    (hL : ∀ op a, e = App (Val (.GoInstruction op)) (Val a) →
      @GoLocalContext.is_go_step_pure _ L' op a =
        @GoLocalContext.is_go_step_pure _ σ.goState.goLctx op a) :
    HeadStep e (Perennial.setLctx L' σ, g) κ e' (Perennial.setLctx L' σ', g') efs := by
  generalize hs : ((σ, g) : CfgState) = s at h
  generalize hs' : ((σ', g') : CfgState) = s' at h
  cases h with
  | unwind hu =>
    subst hs; simp only [Prod.mk.injEq] at hs'; obtain ⟨rfl, rfl⟩ := hs'; exact .unwind hu
  | base hu hb =>
    subst hs hs'; exact .base hu (hb.setLctx L' hL)

/-- The global state with the prophecy ids `ps` used. -/
def addProphs (ps : List proph_id) (g : GlobalState) : GlobalState :=
  ps.foldr GlobalState.addProph g

theorem mem_addProphs {q : proph_id} {ps : List proph_id} {g : GlobalState} :
    q ∈ (addProphs ps g).usedProphId ↔ q ∈ ps ∨ q ∈ g.usedProphId := by
  induction ps with
  | nil => simp [addProphs]
  | cons p ps ih =>
    simp only [addProphs, List.foldr, GlobalState.addProph] at ih ⊢
    rw [elem_of_union, mem_singletonU, ih]
    simp [or_assoc, eq_comm]

theorem HeadStep.addProphs {e : Expr} {σ σ' : state} {g g' : GlobalState}
    {κ : List Observation} {e' : Expr} {efs : List Expr} {ps : List proph_id}
    (h : HeadStep e (σ, g) κ e' (σ', g') efs) (hnd : ps.Nodup)
    (hps : ∀ p ∈ ps, p ∉ g'.usedProphId) :
    HeadStep e (σ, Perennial.addProphs ps g) κ e' (σ', Perennial.addProphs ps g') efs := by
  induction ps with
  | nil => exact h
  | cons p ps ih =>
    rw [List.nodup_cons] at hnd
    have ih := ih hnd.2 (fun q hq => hps q (List.mem_cons_of_mem _ hq))
    refine HeadStep.addProph ih p ?_
    rw [mem_addProphs]
    rintro (hm | hm)
    · exact hnd.1 hm
    · exact hps p List.mem_cons_self hm

theorem HeadStep.delProphs {e : Expr} {σ : state} {g : GlobalState} {κ : List Observation}
    {e' : Expr} {σg' : CfgState} {efs : List Expr} {ps : List proph_id}
    (h : HeadStep e (σ, Perennial.addProphs ps g) κ e' σg' efs) :
    ∃ κ' e'' σg'' efs', HeadStep e (σ, g) κ' e'' σg'' efs' := by
  induction ps generalizing κ e' σg' efs with
  | nil => exact ⟨_, _, _, _, h⟩
  | cons p ps ih =>
    obtain ⟨κ', e'', σg'', efs', h'⟩ := HeadStep.delProph p h
    exact ih h'

/-- The instrumented state of the real bounded state `s`: the model `L'`, the ids `ps` used. -/
def instrSt (L' : GoLocalContext) (ps : List proph_id) (s : BcfgState) : BcfgState :=
  ((setLctx L' s.1.1, addProphs ps s.1.2), s.2)

/-- A head step changes neither the Go model nor drops a used prophecy id. -/
theorem HeadStep.goLctx {e : Expr} {σg σg' : CfgState} {κ : List Observation} {e' : Expr}
    {efs : List Expr} (h : HeadStep e σg κ e' σg' efs) :
    σg'.1.goState.goLctx = σg.1.goState.goLctx := by
  cases h with
  | unwind => rfl
  | base _ hb =>
    cases hb with
    | ExternalOpS ext op v e' σg σg' hst =>
      obtain ⟨E, hE, h', s', gw', hs, rfl⟩ := hst; rfl
    | _ => rfl

end instrState2

/-! ## Thread-local steps of the bounded language -/

section lsteps
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

theorem fill_eq_fillK (K : List EctxItem) (e : Expr) : EvContext.fill K e = fillK K e := rfl

/-- Steps of one thread that fork nothing. -/
inductive LSteps : Expr → BcfgState → Expr → BcfgState → Prop
  | refl (e : Expr) (s : BcfgState) : LSteps e s e s
  | step {e s κ e' s' e'' s''} :
      (e, s) -<κ>-> (e', s', []) → LSteps e' s' e'' s'' → LSteps e s e'' s''

theorem LSteps.trans {e s e' s' e'' s''} (h1 : LSteps e s e' s') (h2 : LSteps e' s' e'' s'') :
    LSteps e s e'' s'' := by
  induction h1 with
  | refl => exact h2
  | step h _ ih => exact .step h (ih h2)

theorem LSteps.fill (K : List EctxItem) {e s e' s'} (h : LSteps e s e' s') :
    LSteps (fillK K e) s (fillK K e') s' := by
  induction h with
  | refl => exact .refl _ _
  | step h _ ih => exact .step (EctxLanguage.fill_primStep K h) ih

theorem LSteps.pool {e s e' s'} (h : LSteps e s e' s') (t1 t2 : List Expr) :
    ∃ m κs, Language.NSteps m (t1 ++ e :: t2, s) κs (t1 ++ e' :: t2, s') := by
  induction h with
  | refl => exact ⟨0, [], .refl _⟩
  | step h _ ih =>
    obtain ⟨m, κs, H⟩ := ih
    have := Language.Step.atomic h t1 t2
    simp only [List.append_nil] at this
    exact ⟨_, _, .cons this H⟩

theorem LSteps.plain {e1 e2 : Expr} {σg σg' : CfgState} {f : Fuel} {κ : List Observation}
    (hk : redexKind e1 = .plain) (hu : ∀ q, ¬ Unwinds e1 q) (hb : BaseStep e1 σg κ e2 σg' []) :
    LSteps e1 (σg, f) e2 (σg', f) := by
  have hbb : BoundedBaseStep e1 (σg, f) κ e2 (σg', f) [] := .step hk (.base hu hb)
  exact .step (BaseStep.ContextStep.intro (K := []) hbb) (.refl _ _)

/-- The wrapper's frame `[AppRCtx (prophRet #p)]`. -/
abbrev pfItem (p : proph_id) : EctxItem := .AppRCtx (prophRet (Val #p))

/-- **The wrapper's end**: a value (or a panic) leaves the wrapper's frame in plain steps. -/
theorem LSteps.suffix (p : proph_id) (v : val) (σg : CfgState) (f : Fuel) :
    LSteps (fillItem (pfItem p) (Val v)) (σg, f) (Val v) (σg, f) := by
  cases hv : v.isPanic
  · have hpv : (#p : val).isPanic = false := isPanic_intoVal p
    have huv : (#() : val).isPanic = false := isPanic_intoVal ()
    have s1 := LSteps.fill [.AppLCtx v hv] (LSteps.plain (σg := σg) (f := f)
      (e1 := prophRet (Val #p)) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _))
    have s2 := LSteps.plain (σg := σg) (f := f)
      (e1 := App (Val (RecV BAnon "r" (App (Rec BAnon BAnon (Var "r"))
        (ResolveProph (Val #p) (Var "r"))))) (Val v)) rfl (not_unwinds_App_val rfl hv)
      (BaseStep.BetaS BAnon "r" _ v σg)
    have s3 := LSteps.fill [.AppRCtx (Rec BAnon BAnon (Val v))] (LSteps.plain (σg := σg) (f := f)
      (e1 := ResolveProph (Val #p) (Val v)) rfl (not_unwinds_Resolve_val hpv hv)
      (BaseStep.ResolveProphS p v σg))
    have s4 := LSteps.fill [.AppLCtx #() huv] (LSteps.plain (σg := σg) (f := f)
      (e1 := Rec BAnon BAnon (Val v)) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _))
    have s5 := LSteps.plain (σg := σg) (f := f)
      (e1 := App (Val (RecV BAnon BAnon (Val v))) (Val #())) rfl (not_unwinds_App_val rfl huv)
      (BaseStep.BetaS BAnon BAnon (Val v) #() σg)
    simp only [fillK_cons, fillK_nil, fillItem, subst', subst, prophRet, id] at s1 s2 s3 s4 s5 ⊢
    exact s1.trans (s2.trans (s3.trans (s4.trans s5)))
  · obtain ⟨q, rfl⟩ := val.isPanic_eq_true hv
    have hbb : BoundedBaseStep (fillItem (pfItem p) (Val (PanicV q))) (σg, f) []
        (Val (PanicV q)) (σg, f) [] :=
      .step rfl (.unwind ⟨pfItem p, rfl, rfl⟩)
    exact .step (BaseStep.ContextStep.intro (K := []) hbb) (.refl _ _)

/-- **The wrapper's start**: `withProph e` creates the prophecy `p` and reaches `e` in the
wrapper's frame, in plain steps. -/
theorem LSteps.prefix (e : Expr) (σg : CfgState) (f : Fuel) (p : proph_id)
    (hp : p ∉ σg.2.usedProphId) :
    LSteps (withProph e) (σg, f) (fillItem (pfItem p) e) (σg.addProph p, f) := by
  have hpv : (#p : val).isPanic = false := isPanic_intoVal p
  have s1 := LSteps.fill [.AppRCtx (Val prophWrapper)] (LSteps.plain (σg := σg) (f := f)
    (e1 := Rec BAnon BAnon e) rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS BAnon BAnon e σg))
  have s2 := LSteps.plain (σg := σg) (f := f)
    (e1 := App (Val prophWrapper) (Val (RecV BAnon BAnon e))) rfl (not_unwinds_App_val rfl rfl)
    (BaseStep.BetaS BAnon "t" _ (RecV BAnon BAnon e) σg)
  have s3 := LSteps.fill [.AppRCtx (Rec BAnon "p" (App (prophRet (Var "p"))
      (App (Val (RecV BAnon BAnon e)) (Val unitV))))] (LSteps.plain (f := f)
    (e1 := NewProph) rfl not_unwinds_NewProph (BaseStep.NewProphS p σg hp))
  have s4 := LSteps.fill [.AppLCtx #p hpv] (LSteps.plain (σg := σg.addProph p) (f := f)
    (e1 := Rec BAnon "p" (App (prophRet (Var "p")) (App (Val (RecV BAnon BAnon e)) (Val unitV))))
    rfl (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _))
  have s5 := LSteps.plain (σg := σg.addProph p) (f := f)
    (e1 := App (Val (RecV BAnon "p" (App (prophRet (Var "p"))
      (App (Val (RecV BAnon BAnon e)) (Val unitV))))) (Val #p))
    rfl (not_unwinds_App_val rfl hpv) (BaseStep.BetaS BAnon "p" _ #p _)
  have s6 := LSteps.fill [pfItem p] (LSteps.plain (σg := σg.addProph p) (f := f)
    (e1 := App (Val (RecV BAnon BAnon e)) (Val unitV))
    rfl (not_unwinds_App_val rfl rfl) (BaseStep.BetaS BAnon BAnon e unitV _))
  simp only [fillK_cons, fillK_nil, fillItem, subst', subst, prophRet, prophWrapper, withProph,
    id] at s1 s2 s3 s4 s5 s6 ⊢
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans s6))))

end lsteps

/-! ## The threads' relation: the real frames, with the wrapper's inserted -/

section ctxrel
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

/-- `CtxRel K K'`: `K'` is `K` with wrapper frames `pfItem p` inserted. -/
inductive CtxRel : List EctxItem → List EctxItem → Prop
  | nil : CtxRel [] []
  | same (Ki : EctxItem) {K K' : List EctxItem} : CtxRel K K' → CtxRel (Ki :: K) (Ki :: K')
  | proph (p : proph_id) {K K' : List EctxItem} : CtxRel K K' → CtxRel K (pfItem p :: K')

theorem CtxRel.rfl' : ∀ (K : List EctxItem), CtxRel K K
  | [] => .nil
  | Ki :: K => .same Ki (CtxRel.rfl' K)

theorem CtxRel.prefix : ∀ (K1 : List EctxItem) {K K' : List EctxItem}, CtxRel K K' →
    CtxRel (K1 ++ K) (K1 ++ K')
  | [], _, _, h => h
  | Ki :: K1, _, _, h => .same Ki (CtxRel.prefix K1 h)

/-- **Leaving the wrapper's frames** above a value, up to the next real frame `Ki`. -/
theorem CtxRel.strip {Ki : EctxItem} {K Kx : List EctxItem} (h : CtxRel (Ki :: K) Kx) (v : val)
    (σg : CfgState) (f : Fuel) :
    ∃ Kx', CtxRel K Kx' ∧
      LSteps (fillK Kx (Val v)) (σg, f) (fillK Kx' (fillItem Ki (Val v))) (σg, f) := by
  generalize hK : Ki :: K = K0 at h
  induction h with
  | nil => cases hK
  | same Kj h _ =>
    cases hK
    exact ⟨_, h, .refl _ _⟩
  | proph p h ih =>
    obtain ⟨Kx', h', hs⟩ := ih hK
    exact ⟨Kx', h', (LSteps.fill _ (LSteps.suffix p v σg f)).trans hs⟩

/-- Leaving all the wrapper's frames of a value. -/
theorem CtxRel.stripAll {Kx : List EctxItem} (h : CtxRel [] Kx) (v : val) (σg : CfgState)
    (f : Fuel) : LSteps (fillK Kx (Val v)) (σg, f) (Val v) (σg, f) := by
  generalize hK : ([] : List EctxItem) = K0 at h
  induction h with
  | nil => exact .refl _ _
  | same Kj h _ => cases hK
  | proph p h ih => exact (LSteps.fill _ (LSteps.suffix p v σg f)).trans (ih hK)

/-- The body of `prophFnV impl` once applied to `v1`. -/
def prophFnBody (impl v1 : val) : Expr :=
  withProph (App (App (Val impl) (Val v1)) (Var "$a2"))

theorem LSteps.callA (impl v1 : val) (h1 : v1.isPanic = false) (σg : CfgState) (f : Fuel) :
    LSteps (App (Val (prophFnV impl)) (Val v1)) (σg, f)
      (Val (RecV BAnon "$a2" (prophFnBody impl v1))) (σg, f) := by
  have s1 := LSteps.plain (σg := σg) (f := f) (e1 := App (Val (prophFnV impl)) (Val v1)) rfl
    (not_unwinds_App_val rfl h1) (BaseStep.BetaS BAnon "$a1" _ v1 σg)
  have s2 := LSteps.plain (σg := σg) (f := f) (e1 := Rec BAnon "$a2" (prophFnBody impl v1)) rfl
    (not_unwinds_Rec _ _ _) (BaseStep.RecS _ _ _ _)
  simp only [subst', subst, prophFnV, prophFnBody, withProph, id] at s1 s2 ⊢
  exact s1.trans s2

theorem LSteps.callB (impl v1 v2 : val) (h2 : v2.isPanic = false) (σg : CfgState) (f : Fuel)
    (p : proph_id) (hp : p ∉ σg.2.usedProphId) :
    LSteps (App (Val (RecV BAnon "$a2" (prophFnBody impl v1))) (Val v2)) (σg, f)
      (fillItem (pfItem p) (App (App (Val impl) (Val v1)) (Val v2))) (σg.addProph p, f) := by
  have s1 := LSteps.plain (σg := σg) (f := f)
    (e1 := App (Val (RecV BAnon "$a2" (prophFnBody impl v1))) (Val v2)) rfl
    (not_unwinds_App_val rfl h2) (BaseStep.BetaS BAnon "$a2" _ v2 σg)
  have s2 := LSteps.prefix (App (App (Val impl) (Val v1)) (Val v2)) σg f p hp
  simp only [subst', subst, prophFnBody, withProph, id] at s1 s2 ⊢
  exact s1.trans s2

/-- **A call of the instrumented function**: from its resolution to `prophFnV impl` in the
call's context (up to the wrapper's frames), plain steps reach `impl` applied to the
arguments, in a new wrapper frame. -/
theorem LSteps.call (impl v1 : val) (h1 : v1.isPanic = false) (v2 : val)
    (h2 : v2.isPanic = false) {K3 Kx : List EctxItem}
    (hrel : CtxRel (.AppLCtx v1 h1 :: .AppLCtx v2 h2 :: K3) Kx) (σg : CfgState) (f : Fuel)
    (p : proph_id) (hp : p ∉ σg.2.usedProphId) :
    ∃ Kx3, CtxRel K3 Kx3 ∧
      LSteps (fillK Kx (Val (prophFnV impl))) (σg, f)
        (fillK (pfItem p :: Kx3) (App (App (Val impl) (Val v1)) (Val v2))) (σg.addProph p, f) := by
  obtain ⟨Kx1, hr1, hs1⟩ := hrel.strip (prophFnV impl) σg f
  obtain ⟨Kx3, hr3, hs3⟩ := hr1.strip (RecV BAnon "$a2" (prophFnBody impl v1)) σg f
  refine ⟨Kx3, hr3, hs1.trans (((LSteps.callA impl v1 h1 σg f).fill Kx1).trans
    (hs3.trans ?_))⟩
  exact (LSteps.callB impl v1 v2 h2 σg f p hp).fill Kx3

end ctxrel

/-! ## The simulation -/

section sim
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

/-- The instruction value that resolves `f`. -/
abbrev giOf (f : GoString) : val := .GoInstruction (.FuncResolve f [])

theorem fillK_inj (K : List EctxItem) {e1 e2 : Expr} (h : fillK K e1 = fillK K e2) : e1 = e2 := by
  induction K generalizing e1 e2 with
  | nil => exact h
  | cons Ki K ih => exact fillItem_inj Ki (ih h)

theorem toVal_fillK_cons (Ki : EctxItem) (K : List EctxItem) (e : Expr) :
    toVal (fillK (Ki :: K) e) = none := by
  induction K generalizing e Ki with
  | nil => exact toVal_fillItem Ki e
  | cons Kj K ih => exact ih Kj (fillItem Ki e)

theorem toVal_fillK_none {K : List EctxItem} {e : Expr} (h : toVal e = none) :
    toVal (fillK K e) = none := by
  cases K with
  | nil => exact h
  | cons Ki K => exact toVal_fillK_cons Ki K e

/-- A thread of the real execution and of the instrumented one. -/
def ThreadRel (er ei : Expr) : Prop :=
  ∃ Kr Ki e0, er = fillK Kr e0 ∧ ei = fillK Ki e0 ∧ CtxRel Kr Ki

theorem ThreadRel.rfl' (e : Expr) : ThreadRel e e := ⟨[], [], e, rfl, rfl, .nil⟩

/-- **Normalization**: the instrumented thread leaves the wrapper's frames above a value that
the real thread's next frame consumes; then the related expression is not a value. -/
theorem ThreadRel.normalize {er ei : Expr} (h : ThreadRel er ei) (hv : toVal er = none)
    (σg : CfgState) (f : Fuel) :
    ∃ Kr Ki e0 ei', er = fillK Kr e0 ∧ toVal e0 = none ∧ CtxRel Kr Ki ∧
      LSteps ei (σg, f) ei' (σg, f) ∧ ei' = fillK Ki e0 := by
  obtain ⟨Kr, Ki, e0, rfl, rfl, hr⟩ := h
  cases h0 : toVal e0 with
  | none => exact ⟨Kr, Ki, e0, _, rfl, h0, hr, .refl _ _, rfl⟩
  | some v =>
    have := of_to_val h0; subst this
    cases Kr with
    | nil => simp at hv
    | cons Kj Kr =>
      obtain ⟨Ki', hr', hs⟩ := hr.strip v σg f
      exact ⟨Kr, Ki', fillItem Kj (Val v), _, rfl, toVal_fillItem _ _, hr', hs, rfl⟩

theorem HeadStep.toInstr (L' : GoLocalContext) {e : Expr} {σg σg' : CfgState}
    {κ : List Observation} {e' : Expr} {efs : List Expr} (h : HeadStep e σg κ e' σg' efs)
    (hL : ∀ op a, e = App (Val (.GoInstruction op)) (Val a) →
      @GoLocalContext.is_go_step_pure _ L' op a =
        @GoLocalContext.is_go_step_pure _ σg.1.goState.goLctx op a)
    {ps : List proph_id} (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∉ σg'.2.usedProphId) :
    HeadStep e (Perennial.setLctx L' σg.1, Perennial.addProphs ps σg.2) κ e'
      (Perennial.setLctx L' σg'.1, Perennial.addProphs ps σg'.2) efs := by
  obtain ⟨σ, g⟩ := σg; obtain ⟨σ', g'⟩ := σg'
  exact (h.setLctx L' hL).addProphs hnd hps

theorem BoundedBaseStep.toInstr (L' : GoLocalContext) {e : Expr} {s s' : BcfgState}
    {κ : List Observation} {e' : Expr} {efs : List Expr} (h : BoundedBaseStep e s κ e' s' efs)
    (hL : ∀ op a, e = App (Val (.GoInstruction op)) (Val a) →
      @GoLocalContext.is_go_step_pure _ L' op a =
        @GoLocalContext.is_go_step_pure _ s.1.1.goState.goLctx op a)
    {ps : List proph_id} (hnd : ps.Nodup) (U : GSet proph_id)
    (hU : ∀ q ∈ s.1.2.usedProphId, q ∈ U) (hU' : ∀ q ∈ s'.1.2.usedProphId, q ∈ U)
    (hps : ∀ p ∈ ps, p ∉ U) :
    BoundedBaseStep e (instrSt L' ps s) κ e' (instrSt L' ps s') efs := by
  cases h with
  | step hk hh => exact .step hk (hh.toInstr L' hL hnd fun p hp hm => hps p hp (hU' p hm))
  | tick hk hh => exact .tick hk (hh.toInstr L' hL hnd fun p hp hm => hps p hp (hU' p hm))
  | stutter hk hh =>
    have hg := hh.counted_global hk
    exact .stutter hk (hh.toInstr L' hL hnd fun p hp hm => hps p hp (hU p (hg ▸ hm)))
  | fork hh => exact .fork (hh.toInstr L' hL hnd fun p hp hm => hps p hp (hU' p hm))
  | forkStutter => exact .forkStutter
  | exit hh => exact .exit (hh.toInstr L' hL hnd fun p hp hm => hps p hp (hU' p hm))

/-- Every thread of the configuration keeps calls in position. -/
def PoolOk (gi : val) (t : List Expr) : Prop := ∀ e ∈ t, ok gi 0 e

variable (f : GoString) (impl : val) (L : GoLocalContext)

theorem state_packageState_self (σ : state) :
    { σ with goState := { σ.goState with packageState := σ.goState.packageState } } = σ := by
  obtain ⟨h, ⟨L, ps⟩, w, t⟩ := σ; rfl

/-- A step of the resolution of `f`: a stutter, or `impl`. -/
theorem BoundedBaseStep.patched {s s' : BcfgState} {κ : List Observation} {e' : Expr}
    {efs : List Expr} (h : BoundedBaseStep (App (Val (giOf f)) (Val unitV)) s κ e' s' efs)
    (hL : s.1.1.goState.goLctx = L)
    (Himpl : ∀ e, L.is_go_step_pure (.FuncResolve f []) unitV e ↔ e = Val impl) :
    (e' = App (Val (giOf f)) (Val unitV) ∧ s' = s ∧ efs = [] ∧ κ = []) ∨
      (∃ c t, s.2 = ⟨c + 1, t⟩ ∧ s' = (s.1, ⟨c, t⟩) ∧ e' = Val impl ∧ efs = [] ∧ κ = []) := by
  cases h with
  | step hk _ => simp [redexKind] at hk
  | tick hk hh =>
    right
    cases hh with
    | unwind hu => exact absurd hu (not_unwinds_GoInstruction rfl _)
    | base _ hb =>
      cases hb with
      | GoInstructionS op arg e' s' σg hst =>
        unfold IsGoStep at hst
        simp only at hst
        obtain ⟨hst, rfl⟩ := hst
        rw [hL, Himpl] at hst
        subst hst
        refine ⟨_, _, rfl, ?_, rfl, rfl, rfl⟩
        rw [state_packageState_self]
  | stutter => left; exact ⟨rfl, rfl, rfl, rfl⟩

/-- **One step of one thread** of the real execution (in the model `L`, where `f` resolves to
`impl`) is matched by steps of the instrumented thread (in the patched model, with the ids `ps`
used): the related thread after them, the same forked threads. -/
theorem sim_step {er ei er' : Expr} {sr sr' : BcfgState} {κ : List Observation}
    {efs : List Expr} (hstep : (er, sr) -<κ>-> (er', sr', efs)) (hrel : ThreadRel er ei)
    (hok : ok (giOf f) 0 er) (hL : sr.1.1.goState.goLctx = L)
    (Himpl : ∀ e, L.is_go_step_pure (.FuncResolve f []) unitV e ↔ e = Val impl)
    (ps : List proph_id) (hnd : ps.Nodup) (U : GSet proph_id)
    (hU : ∀ q ∈ sr'.1.2.usedProphId, q ∈ U) (hps : ∀ p ∈ ps, p ∉ U) :
    ∃ ei' ps', ThreadRel er' ei' ∧ ps'.Nodup ∧ (∀ p ∈ ps', p ∉ U) ∧
      ∀ t1 t2, ∃ m κs, Language.NSteps m
        (t1 ++ ei :: t2, instrSt (patchLctx L f (prophFnV impl)) ps sr) κs
        (t1 ++ ei' :: t2 ++ efs, instrSt (patchLctx L f (prophFnV impl)) ps' sr') := by
  have hv : toVal er = none := Language.val_stuck hstep
  obtain ⟨σg, fu⟩ := sr
  obtain ⟨Kr, Ki, e0, ei1, her, h0, hr, hs1, rfl⟩ :=
    hrel.normalize hv (instrSt (patchLctx L f (prophFnV impl)) ps (σg, fu)).1 fu
  subst her
  generalize hE : fillK Kr e0 = er0 at hstep
  cases hstep with
  | intro hb =>
  rename_i e1 e2 K
  obtain ⟨K'', rfl⟩ := EctxLanguage.step_by_val (K' := Kr) hE h0 hb
  have he0 : e0 = fillK K'' e1 := by
    apply fillK_inj Kr
    rw [hE]; exact fillK_append K'' Kr e1
  subst he0
  have hrel' : CtxRel (K'' ++ Kr) (K'' ++ Ki) := CtxRel.prefix K'' hr
  have hpool1 := fun t1 t2 => hs1.pool t1 t2
  by_cases hpat : e1 = App (Val (giOf f)) (Val unitV)
  · subst hpat
    rcases BoundedBaseStep.patched f impl L hb hL Himpl with
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨c, t, hfu, hs', rfl, rfl, rfl⟩
    · refine ⟨_, ps, ⟨Kr, Ki, _, fillK_append K'' Kr _, rfl, hr⟩, hnd, hps, fun t1 t2 => ?_⟩
      obtain ⟨m, κs, H⟩ := hpool1 t1 t2
      exact ⟨m, κs, by rw [List.append_nil]; exact H⟩
    · -- the resolution of `f`: the instrumented thread resolves it to `prophFnV impl`, and calls it
      rw [← fillK_append] at hok
      obtain ⟨v1, h1, v2, h2, K3, hK3⟩ := ctx_of_ok_call (o := .FuncResolve f []) hok
      subst hfu
      obtain ⟨p, hp⟩ := exists_fresh_proph (addProphs ps { σg.2 with usedProphId := U }).usedProphId
      rw [mem_addProphs] at hp
      simp only [not_or] at hp
      have hpU : p ∉ σg.2.usedProphId := fun hm => hp.2 (hU p (by rw [hs']; exact hm))
      subst hs'
      have hIs : @IsGoStep _ _ (patchLctx L f (prophFnV impl)) (.FuncResolve f []) unitV
          (Val (prophFnV impl)) (setLctx (patchLctx L f (prophFnV impl)) σg.1).goState.packageState
          (setLctx (patchLctx L f (prophFnV impl)) σg.1).goState.packageState := by
        unfold IsGoStep; simp only [patchLctx_nil]; simp
      have hbs := BaseStep.GoInstructionS (.FuncResolve f []) unitV (Val (prophFnV impl)) _
        (setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2) hIs
      rw [state_packageState_self] at hbs
      have hbb : BoundedBaseStep (App (Val (giOf f)) (Val unitV))
          ((setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2), ⟨c + 1, t⟩) []
          (Val (prophFnV impl))
          ((setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2), ⟨c, t⟩) [] :=
        .tick rfl (.base (not_unwinds_GoInstruction rfl) hbs)
      have hst : (fillK (K'' ++ Ki) (App (Val (giOf f)) (Val unitV)),
          (((setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2), ⟨c + 1, t⟩) :
            BcfgState)) -<([] : List Observation)>->
          (fillK (K'' ++ Ki) (Val (prophFnV impl)),
            ((setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2), ⟨c, t⟩), []) :=
        BaseStep.ContextStep.intro (K := K'' ++ Ki) hbb
      have hrel3 : CtxRel (.AppLCtx v1 h1 :: .AppLCtx v2 h2 :: K3) (K'' ++ Ki) := hK3 ▸ hrel'
      obtain ⟨Kx3, hr3, hs3⟩ := LSteps.call impl v1 h1 v2 h2 hrel3
        (setLctx (patchLctx L f (prophFnV impl)) σg.1, addProphs ps σg.2) ⟨c, t⟩ p
        (by rw [mem_addProphs]; simp [hp.1, hpU])
      refine ⟨fillK (pfItem p :: Kx3) (App (App (Val impl) (Val v1)) (Val v2)), p :: ps, ?_,
        List.nodup_cons.2 ⟨hp.1, hnd⟩, ?_, fun t1 t2 => ?_⟩
      · refine ⟨K3, pfItem p :: Kx3, _, ?_, rfl, .proph p hr3⟩
        show fillK (K'' ++ Kr) (Val impl) = _
        rw [hK3]; rfl
      · intro q hq
        rcases List.mem_cons.1 hq with rfl | hq
        · exact hp.2
        · exact hps q hq
      · obtain ⟨m1, κs1, H1⟩ := hpool1 t1 t2
        have H2 := Language.Step.atomic hst t1 t2
        obtain ⟨m3, κs3, H3⟩ := hs3.pool t1 t2
        rw [List.append_nil] at H2 ⊢
        rw [fillK_append] at H2
        exact ⟨_, _, nsteps_append H1 (.cons H2 H3)⟩
  · -- any other step: the same step, in the instrumented state
    have hL' : ∀ op a, e1 = App (Val (.GoInstruction op)) (Val a) →
        @GoLocalContext.is_go_step_pure _ (patchLctx L f (prophFnV impl)) op a =
          @GoLocalContext.is_go_step_pure _ (σg, fu).1.1.goState.goLctx op a := by
      intro op a he
      rw [hL]
      apply patchLctx_other
      rintro ⟨rfl, rfl⟩; exact hpat he
    have hb0 : BoundedBaseStep e1 (σg, fu) κ e2 sr' efs := hb
    have hU0 : ∀ q ∈ (σg, fu).1.2.usedProphId, q ∈ U :=
      fun q hq => hU q (BoundedBaseStep.usedProph_mono hb0 q hq)
    have hb' := BoundedBaseStep.toInstr (patchLctx L f (prophFnV impl)) hb0 hL' hnd U hU0 hU hps
    have hst : (fillK (K'' ++ Ki) e1, instrSt (patchLctx L f (prophFnV impl)) ps (σg, fu))
        -<κ>-> (fillK (K'' ++ Ki) e2, instrSt (patchLctx L f (prophFnV impl)) ps sr', efs) :=
      BaseStep.ContextStep.intro (K := K'' ++ Ki) hb'
    refine ⟨fillK (K'' ++ Ki) e2, ps, ⟨Kr, Ki, fillK K'' e2, fillK_append K'' Kr _,
      fillK_append K'' Ki _, hr⟩, hnd, hps, fun t1 t2 => ?_⟩
    obtain ⟨m1, κs1, H1⟩ := hpool1 t1 t2
    have H2 := Language.Step.atomic hst t1 t2
    rw [fillK_append] at H2
    exact ⟨_, _, nsteps_append H1 (.cons H2 (.refl _))⟩

end sim

/-! ## The simulation of an execution -/

section simExec
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

/-- A bounded step is a stutter, or a head step. -/
theorem BoundedBaseStep.inv {e : Expr} {s s' : BcfgState} {κ : List Observation} {e' : Expr}
    {efs : List Expr} (h : BoundedBaseStep e s κ e' s' efs) :
    (e' = e ∧ s'.1 = s.1 ∧ efs = []) ∨ HeadStep e s.1 κ e' s'.1 efs := by
  cases h with
  | step _ hh => exact .inr hh
  | tick _ hh => exact .inr hh
  | stutter => exact .inl ⟨rfl, rfl, rfl⟩
  | fork hh => exact .inr hh
  | forkStutter => exact .inl ⟨rfl, rfl, rfl⟩
  | exit hh => exact .inr hh

variable (f : GoString) (impl : val) (L : GoLocalContext)

/-- The real configuration's invariant: calls of `f` in position, the model `L`. -/
def RealInv (ρ : List Expr × BcfgState) : Prop :=
  PoolOk (giOf f) ρ.1 ∧ heapOk (giOf f) ρ.2.1.1.heap ∧ ρ.2.1.1.goState.goLctx = L

theorem RealInv.step {ρ ρ' : List Expr × BcfgState} {κ : List Observation}
    (h : Language.Step ρ κ ρ') (hinv : RealInv f L ρ) (hM : GoodModel (giOf f) L)
    (hX : GoodExts (giOf f)) (hI : IntoValOk (giOf f)) : RealInv f L ρ' := by
  obtain ⟨hp, hh, hL⟩ := hinv
  cases h with
  | atomic H t1 t2 =>
  rename_i e σ e' σ' efs
  generalize hE : e = e0 at H
  cases H with
  | intro hb =>
  rename_i e1 e2 K
  subst hE
  have hok := hp _ (List.mem_append_right _ List.mem_cons_self)
  rw [fill_eq_fillK, ok_fillK] at hok
  rcases BoundedBaseStep.inv hb with ⟨rfl, hs, rfl⟩ | hh'
  · refine ⟨?_, hs ▸ hh, hs ▸ hL⟩
    intro e he
    simp only [List.append_nil] at he
    rcases List.mem_append.1 he with he | he
    · exact hp e (List.mem_append_left _ he)
    rcases List.mem_cons.1 he with rfl | he
    · rw [fill_eq_fillK, ok_fillK]; exact hok
    · exact hp e (List.mem_append_right _ (List.mem_cons_of_mem _ he))
  · obtain ⟨h1, h2, h3⟩ := hh'.keeps_ok _ hok.2 hh (hL ▸ hM) hX hI ⟨_, rfl⟩
    refine ⟨?_, h2, hh'.goLctx.trans hL⟩
    intro e he
    rcases List.mem_append.1 he with he | he
    · rcases List.mem_append.1 he with he | he
      · exact hp e (List.mem_append_left _ he)
      rcases List.mem_cons.1 he with rfl | he
      · rw [fill_eq_fillK, ok_fillK]; exact ⟨hok.1, h1⟩
      · exact hp e (List.mem_append_right _ (List.mem_cons_of_mem _ he))
    · exact h3 e he

theorem Forall₂_split {A B : Type} {R : A → B → Prop} {t1 : List A} {a : A} {t2 : List A}
    {l : List B} (h : List.Forall₂ R (t1 ++ a :: t2) l) :
    ∃ l1 b l2, l = l1 ++ b :: l2 ∧ List.Forall₂ R t1 l1 ∧ R a b ∧ List.Forall₂ R t2 l2 := by
  induction t1 generalizing l with
  | nil =>
    cases h with
    | cons hab h2 => exact ⟨[], _, _, rfl, .nil, hab, h2⟩
  | cons x t1 ih =>
    cases h with
    | cons hx h' =>
      obtain ⟨l1, b, l2, rfl, h1, hab, h2⟩ := ih h'
      exact ⟨_ :: l1, b, l2, rfl, .cons hx h1, hab, h2⟩

theorem Forall₂_refl {A : Type} {R : A → A → Prop} (hR : ∀ a, R a a) :
    ∀ (l : List A), List.Forall₂ R l l
  | [] => .nil
  | a :: l => .cons (hR a) (Forall₂_refl hR l)

/-- **The simulation**: an execution of the bounded language in the model `L` (keeping calls of
`f` in position) is matched by an execution in the patched model, with related threads. -/
theorem sim_nsteps (Himpl : ∀ e, L.is_go_step_pure (.FuncResolve f []) unitV e ↔ e = Val impl)
    (hM : GoodModel (giOf f) L) (hX : GoodExts (giOf f)) (hI : IntoValOk (giOf f))
    {n : Nat} {ρ ρ' : List Expr × BcfgState} {κs : List Observation}
    (h : Language.NSteps n ρ κs ρ') (U : GSet proph_id)
    (hU : ∀ q ∈ ρ'.2.1.2.usedProphId, q ∈ U) (hinv : RealInv f L ρ)
    (ti : List Expr) (hrel : List.Forall₂ ThreadRel ρ.1 ti)
    (ps : List proph_id) (hnd : ps.Nodup) (hps : ∀ p ∈ ps, p ∉ U) :
    ∃ ti' ps' m κs', Language.NSteps m (ti, instrSt (patchLctx L f (prophFnV impl)) ps ρ.2) κs'
        (ti', instrSt (patchLctx L f (prophFnV impl)) ps' ρ'.2) ∧
      List.Forall₂ ThreadRel ρ'.1 ti' ∧ RealInv f L ρ' := by
  induction h generalizing ti ps with
  | refl => exact ⟨ti, ps, 0, [], .refl _, hrel, hinv⟩
  | @cons n ρ₁ ρ₂ ρ₃ obs obs' hs hrest ih =>
    have hU₂ : ∀ q ∈ ρ₂.2.1.2.usedProphId, q ∈ U :=
      fun q hq => hU q (nsteps_usedProph_mono hrest q hq)
    have hinv₂ := RealInv.step f L hs hinv hM hX hI
    cases hs with
    | atomic H t1 t2 =>
    rename_i efs
    obtain ⟨l1, ei, l2, rfl, h1, hei, h2⟩ := Forall₂_split hrel
    have hok := hinv.1 _ (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨ei', ps', hrel', hnd', hps', hsteps⟩ :=
      sim_step f impl L H hei hok hinv.2.2 Himpl ps hnd U hU₂ hps
    obtain ⟨m1, κs1, H1⟩ := hsteps l1 l2
    have hrel₂ : List.Forall₂ ThreadRel (t1 ++ _ :: t2 ++ efs) (l1 ++ ei' :: l2 ++ efs) :=
      List.Forall₂.append (List.Forall₂.append h1 (.cons hrel' h2)) (Forall₂_refl ThreadRel.rfl' _)
    obtain ⟨ti', ps'', m2, κs2, H2, hr3, hinv3⟩ := ih hU hinv₂ _ hrel₂ ps' hnd' hps'
    exact ⟨ti', ps'', _, _, nsteps_append H1 H2, hr3, hinv3⟩

end simExec

/-! ## Back to the real execution -/

section back
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open EctxLanguage.Notation

theorem fillItem_panic_noval {Ki Kj : EctxItem} {p : val} {e : Expr}
    (h : fillItem Kj (Val (PanicV p)) = fillItem Ki e) (he : toVal e = none) : False := by
  cases Kj <;> cases Ki <;> simp only [fillItem, reduceCtorEq] at h <;> injections <;>
    subst_vars <;> simp_all [toVal, val.isPanic]

theorem UnrecoveredPanic.val_inv {v : val} (h : UnrecoveredPanic (Val v)) : ∃ p, v = PanicV p := by
  generalize hE : Val v = E at h
  cases h with
  | panic p => injection hE with hE; exact ⟨p, hE⟩
  | frame _ _ => rename_i Ki e _ _; cases Ki <;> simp [fillItem] at hE

theorem UnrecoveredPanic.fillItem_inv {Ki : EctxItem} {e : Expr}
    (h : UnrecoveredPanic (fillItem Ki e)) (he : toVal e = none) :
    Ki.unwinds = true ∧ UnrecoveredPanic e := by
  generalize hE : fillItem Ki e = E at h
  cases h with
  | panic p => cases Ki <;> simp [fillItem] at hE
  | frame hu h' =>
    rename_i Kj e'
    cases he' : toVal e' with
    | none =>
      have := fillItem_no_val_inj Kj Ki he' he hE.symm
      subst this
      have := fillItem_inj Kj hE.symm
      subst this
      exact ⟨hu, h'⟩
    | some v =>
      have := of_to_val he'; subst this
      obtain ⟨p, rfl⟩ := h'.val_inv
      exact (fillItem_panic_noval hE.symm he).elim

/-- The frames of `K` all unwind. -/
def AllUnwind (K : List EctxItem) : Prop := ∀ Ki ∈ K, Ki.unwinds = true

theorem UnrecoveredPanic.fillK_inv : ∀ {K : List EctxItem} {e : Expr},
    UnrecoveredPanic (fillK K e) → toVal e = none → AllUnwind K ∧ UnrecoveredPanic e
  | [], _, h, _ => ⟨by simp [AllUnwind], h⟩
  | Ki :: K, e, h, he => by
    obtain ⟨h1, h2⟩ := UnrecoveredPanic.fillK_inv (K := K) h (toVal_fillItem Ki e)
    obtain ⟨h3, h4⟩ := h2.fillItem_inv he
    refine ⟨?_, h4⟩
    intro Kj hKj
    rcases List.mem_cons.1 hKj with rfl | hKj
    · exact h3
    · exact h1 Kj hKj

theorem UnrecoveredPanic.fillK_ctxRel {Kr Ki : List EctxItem} (hr : CtxRel Kr Ki)
    (hu : AllUnwind Kr) {e : Expr} (h : UnrecoveredPanic e) : UnrecoveredPanic (fillK Ki e) := by
  induction hr generalizing e with
  | nil => exact h
  | same Kj _ ih =>
    exact ih (fun K hK => hu K (List.mem_cons_of_mem _ hK)) (.frame (hu Kj List.mem_cons_self) h)
  | proph p _ ih => exact ih hu (.frame rfl h)

variable (f : GoString) (impl : val) (L : GoLocalContext)

/-- A head step of the instrumented state is backed by one of the real state. -/
theorem HeadStep.fromInstr {e : Expr} {σ : state} {g : GlobalState} {ps : List proph_id}
    {κ : List Observation} {e' : Expr} {σg' : CfgState} {efs : List Expr}
    (h : HeadStep e (Perennial.setLctx (patchLctx L f (prophFnV impl)) σ,
      Perennial.addProphs ps g) κ e' σg' efs)
    (hL : σ.goState.goLctx = L)
    (Himpl : ∀ e, L.is_go_step_pure (.FuncResolve f []) unitV e ↔ e = Val impl) :
    ∃ κ' e'' σg'' efs', HeadStep e (σ, g) κ' e'' σg'' efs' := by
  obtain ⟨κ₁, e₁, σg₁, efs₁, h₁⟩ := HeadStep.delProphs h
  by_cases hpat : e = App (Val (giOf f)) (Val unitV)
  · subst hpat
    have hIs : @IsGoStep _ _ σ.goState.goLctx (.FuncResolve f []) unitV (Val impl)
        σ.goState.packageState σ.goState.packageState := by
      unfold IsGoStep; simp only; rw [hL, Himpl]; simp
    exact ⟨_, _, _, _, .base (not_unwinds_GoInstruction rfl)
      (BaseStep.GoInstructionS _ _ _ _ (σ, g) hIs)⟩
  · obtain ⟨σ₁, g₁⟩ := σg₁
    have h₂ := HeadStep.setLctx L h₁ (fun op a he => by
      exact (patchLctx_other L f _ op a (by rintro ⟨rfl, rfl⟩; exact hpat he)).symm)
    rw [setLctx_setLctx, ← hL, setLctx_self] at h₂
    exact ⟨_, _, _, _, h₂⟩

theorem Forall₂_mem {A B : Type} {R : A → B → Prop} {l1 : List A} {l2 : List B}
    (h : List.Forall₂ R l1 l2) {a : A} (ha : a ∈ l1) :
    ∃ m1 b m2, l2 = m1 ++ b :: m2 ∧ R a b := by
  induction h with
  | nil => cases ha
  | @cons x y l1 l2 hxy _ ih =>
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨[], y, l2, rfl, hxy⟩
    · obtain ⟨m1, b, m2, rfl, hab⟩ := ih ha
      exact ⟨y :: m1, b, m2, rfl, hab⟩

end back

/-! ## The theorem -/

section adequacy
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] {GF : BundledGFunctors}

open EctxLanguage.Notation

/-- **Adequacy of a program from a WP in which the function `f` runs instrumented**: the
conclusions of `goose_adequacy` about the real executions of `e` in the Go model of `σ` (in which
`f` resolves to `impl`), from a WP of `e` in the patched model, where `f` resolves to
`prophFnV impl` (its body under a prophecy of its result). The program keeps `f`'s calls in
position (`ok`: checked on `e`, given of the model's results `GoodModel`, the extensions
`GoodExts`, the basic values `IntoValOk` and the initial heap). -/
theorem goose_adequacy_funcProph [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state)
    (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p)) (f : GoString) (impl : val)
    (Himpl : ∀ e, σ.goState.goLctx.is_go_step_pure (.FuncResolve f []) unitV e ↔ e = Val impl)
    (hM : GoodModel (giOf f) σ.goState.goLctx) (hX : GoodExts (giOf f))
    (hI : IntoValOk (giOf f)) (he : ok (giOf f) 0 e) (hheap : heapOk (giOf f) σ.heap)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = patchLctx σ.goState.goLctx f (prophFnV impl) →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  have Hadeq := goose_adequacy_blang N T (by omega) hT e
    (setLctx (patchLctx σ.goState.goLctx f (prophFnV impl)) σ) g φ Hinitg Hinit Hwp
  -- the real execution in the bounded language
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  -- the instrumented execution
  obtain ⟨ti, ps, m, κs', Hi, hrel, hinv⟩ := sim_nsteps f impl σ.goState.goLctx Himpl hM hX hI Hb
    σ2.2.usedProphId (fun q hq => hq)
    ⟨by simpa [PoolOk] using he, hheap, rfl⟩ [e] (Forall₂_refl ThreadRel.rfl' _) []
    List.nodup_nil (by simp)
  have Hrtc : ∀ {m' κs'' ρ}, Language.NSteps m'
      (ti, instrSt (patchLctx σ.goState.goLctx f (prophFnV impl)) ps ((σ2, ⟨c, t⟩) : BcfgState))
      κs'' ρ →
      ([e], (((setLctx (patchLctx σ.goState.goLctx f (prophFnV impl)) σ, g), ⟨N - 1, T - 2⟩) :
        BcfgState)) -·->ₜₚ* ρ := by
    intro m' κs'' ρ Hm
    exact (Language.erasedStep_nSteps _ _).mpr ⟨_, _, nsteps_append Hi Hm⟩
  refine ⟨?_, ?_, ?_⟩
  · -- the result: leave the main thread's wrapper frames
    rintro v t2' rfl
    cases hrel with
    | cons hr0 hrest =>
    rename_i ei ti'
    obtain ⟨Kr, Ki, e0, hKr, rfl, hr⟩ := hr0
    cases Kr with
    | cons Kj Kr => have := toVal_fillK_cons Kj Kr e0; rw [← hKr] at this; cases this
    | nil =>
    simp only [fillK_nil] at hKr; subst hKr
    obtain ⟨m1, κs1, H1⟩ := (hr.stripAll v _ _).pool [] ti'
    exact Hadeq.adequate_result ti' _ v (Hrtc H1)
  · -- progress: the related thread, normalized, is not stuck
    intro e2 he2
    obtain ⟨m1, ei, m2, rfl, hr2⟩ := Forall₂_mem hrel he2
    cases hv : toVal e2 with
    | some _ => exact .inl (by simp [hv])
    | none =>
    obtain ⟨Kr, Ki, e0, ei', rfl, h0, hr, hs, rfl⟩ := hr2.normalize hv
      (instrSt (patchLctx σ.goState.goLctx f (prophFnV impl)) ps ((σ2, ⟨c, t⟩) : BcfgState)).1
      ⟨c, t⟩
    obtain ⟨m3, κs3, H3⟩ := hs.pool m1 m2
    have hns := Hadeq.adequate_not_stuck _ _ _ rfl (Hrtc H3)
      (List.mem_append_right _ List.mem_cons_self)
    have hns0 := Language.Context.notStuck_fill_inv (K := EvContext.fill Ki) hns
    rcases hns0 with h | ⟨κ1, e3, s3, efs3, H⟩
    · change (toVal e0).isSome = true at h; rw [h0] at h; cases h
    obtain ⟨hb⟩ := H
    rename_i e1 e4 K1
    obtain ⟨κ₁, e₁, σg₁, efs₁, hh⟩ := BoundedBaseStep.real hb
    obtain ⟨σ2l, g2⟩ := σ2
    obtain ⟨κ', e'', σg'', efs', hreal⟩ :=
      HeadStep.fromInstr f impl σ.goState.goLctx hh hinv.2.2 Himpl
    right
    rw [show fillK Kr (EvContext.fill K1 e1) = fillK (K1 ++ Kr) e1 from (fillK_append _ _ _).symm]
    exact ⟨κ', _, σg'', efs', letI := gooseRealEctxiLang;
      BaseStep.ContextStep.intro (K := K1 ++ Kr) hreal⟩
  · -- no unrecovered panic: the related thread has one too
    intro e2 he2 hu
    obtain ⟨m1, ei, m2, rfl, hr2⟩ := Forall₂_mem hrel he2
    cases hv : toVal e2 with
    | some v =>
      have := of_to_val hv; subst this
      obtain ⟨Kr, Ki, e0, hKr, rfl, hr⟩ := hr2
      cases Kr with
      | cons Kj Kr => have := toVal_fillK_cons Kj Kr e0; rw [← hKr] at this; cases this
      | nil =>
      simp only [fillK_nil] at hKr; subst hKr
      exact goose_no_unrecovered_panic_blang N T (by omega) hT e
        (setLctx (patchLctx σ.goState.goLctx f (prophFnV impl)) σ) g φ hφ Hinitg Hinit Hwp
        (nsteps_append Hi (.refl _)) _ (List.mem_append_right _ List.mem_cons_self)
        (UnrecoveredPanic.fillK_ctxRel hr (by simp [AllUnwind]) hu)
    | none =>
      obtain ⟨Kr, Ki, e0, ei', rfl, h0, hr, hs, rfl⟩ := hr2.normalize hv
        (instrSt (patchLctx σ.goState.goLctx f (prophFnV impl)) ps ((σ2, ⟨c, t⟩) : BcfgState)).1
        ⟨c, t⟩
      obtain ⟨m3, κs3, H3⟩ := hs.pool m1 m2
      obtain ⟨hK, hu0⟩ := hu.fillK_inv h0
      exact goose_no_unrecovered_panic_blang N T (by omega) hT e
        (setLctx (patchLctx σ.goState.goLctx f (prophFnV impl)) σ) g φ hφ Hinitg Hinit Hwp
        (nsteps_append Hi H3) _ (List.mem_append_right _ List.mem_cons_self)
        (UnrecoveredPanic.fillK_ctxRel hr hK hu0)

end adequacy

end Perennial
