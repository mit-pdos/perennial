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

end Perennial
