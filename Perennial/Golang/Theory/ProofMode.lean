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
import Perennial.Golang.Theory.TacticsSimpAttr
import Perennial.Golang.Theory.Display
import Perennial.Golang.Theory.IrisTactics
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

theorem decide_inst_eq (p : Prop) (h1 h2 : Decidable p) : @decide p h1 = @decide p h2 := by
  cases h1 <;> cases h2 <;> first | rfl | contradiction

simproc [goose_wp_simp] goose_reduceStrEq (( _ : String) = _) := String.reduceEq
simproc [goose_wp_simp] goose_reduceCtorEq (_ = _) := reduceCtorEq
open Lean Meta in
/-- Evaluate a closed `decide p` (e.g. comparisons of Go string literals in
`exception_seq`), by reduction. -/
simproc [goose_wp_simp] goose_reduceDecide (decide _) := fun e => do
  let_expr Decidable.decide p inst := e | return .continue
  if p.hasMVar then return .continue
  -- free variables are only allowed if they are instances (e.g. the section
  -- variable `[ffi_syntax]` in a word literal), which evaluation does not need
  if p.hasFVar then
    for fv in (collectFVars {} p).fvarIds do
      unless (← isClass? (← fv.getType)).isSome do return .continue
  let r ← withTransparency .default <| whnf e
  if r.isConstOf ``Bool.true ∨ r.isConstOf ``Bool.false then
    return .done { expr := r, proof? := some (mkExpectedPropHint (← mkEqRefl r) (← mkEq e r)) }
  -- the instance may be opaque (e.g. a section variable providing `DecidableEq`):
  -- evaluate with a synthesized instance instead
  if inst.hasFVar then
    let some inst' ← synthInstance? (mkApp (mkConst ``Decidable) p) | return .continue
    let e' := mkApp2 (mkConst ``Decidable.decide) p inst'
    let r ← withTransparency .default <| whnf e'
    if r.isConstOf ``Bool.true ∨ r.isConstOf ``Bool.false then
      let h1 := mkApp3 (mkConst ``decide_inst_eq) p inst inst'
      let h2 := mkExpectedPropHint (← mkEqRefl r) (← mkEq e' r)
      return .done { expr := r, proof? := some (← mkEqTrans h1 h2) }
  return .continue

attribute [goose_wp_simp] List.foldr_cons List.foldr_nil List.foldl_cons List.foldl_nil
  List.zip_cons_cons List.zip_nil_left List.zip_nil_right

attribute [goose_wp_simp] _root_.decide_true _root_.decide_false

attribute [goose_wp_simp] ne_eq not_false_eq_true not_true_eq_false binder.BNamed.injEq
  _root_.and_self _root_.and_true _root_.true_and _root_.and_false _root_.false_and ite_true ite_false if_true if_false
  Bool.false_eq_true

-- Boolean negation of literals (from `GoUnOp GoNot` on a literal).
attribute [goose_wp_simp] Bool.not_true Bool.not_false

/-! ## Substitution lemmas

`wp_pures`/`wp_auto` prove `subst x v e = e'` with these per-constructor lemmas
(see `substPf`) instead of `rfl`: checking `rfl` makes the kernel evaluate
`subst`, deciding `String` equality of every variable and binder through the
UTF-8 encoding (about 2ms per comparison), which made long functions quadratic
with a large constant. String disequalities are proved via `String.ofList`
(`str_ne_of_list_ne`), which the kernel checks without encoding. -/

theorem str_ne_of_list_ne {s t : String} {cs ds : List Char} (hs : s = String.ofList cs)
    (ht : t = String.ofList ds) (h : cs ≠ ds) : s ≠ t := by
  subst hs ht; intro h'; exact h (String.ofList_injective h')
theorem list_char_ne_tail {c : Char} {cs ds : List Char} (h : cs ≠ ds) : c :: cs ≠ c :: ds :=
  fun h' => h (List.cons.inj h').2
theorem list_char_ne_head {c d : Char} {cs ds : List Char} (h : c.toNat ≠ d.toNat) :
    c :: cs ≠ d :: ds := fun h' => h (congrArg Char.toNat (List.cons.inj h').1)
theorem list_char_ne_nil_cons {d : Char} {ds : List Char} : ([] : List Char) ≠ d :: ds := nofun
theorem list_char_ne_cons_nil {c : Char} {cs : List Char} : c :: cs ≠ ([] : List Char) := nofun

section subst_pf
variable [ext : ffi_syntax] {x : String} {v : val}

theorem binder_named_ne_named {y : String} (h : x ≠ y) : BNamed x ≠ BNamed y :=
  fun h' => h (binder.BNamed.inj h')
theorem binder_named_ne_anon : BNamed x ≠ BAnon := nofun

theorem subst_pf_val (w : val) : subst x v (Val w) = Val w := rfl
theorem subst_pf_var_eq : subst x v (Var x) = Val v := by simp [subst]
theorem subst_pf_var_ne {y : String} (h : x ≠ y) : subst x v (Var y) = Var y := by simp [subst, h]
theorem subst_pf_rec {f y : binder} {e e' : expr} (hf : BNamed x ≠ f) (hy : BNamed x ≠ y)
    (he : subst x v e = e') : subst x v (Rec f y e) = Rec f y e' := by
  simp only [subst]; rw [if_pos ⟨hf, hy⟩, he]
theorem subst_pf_rec_f {y : binder} {e : expr} : subst x v (Rec (BNamed x) y e) = Rec (BNamed x) y e := by
  simp [subst]
theorem subst_pf_rec_y {f : binder} {e : expr} : subst x v (Rec f (BNamed x) e) = Rec f (BNamed x) e := by
  simp [subst]
theorem subst_pf_app {a b a' b' : expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (App a b) = App a' b' := by simp only [subst, ha, hb]
theorem subst_pf_if {a b c a' b' c' : expr} (ha : subst x v a = a') (hb : subst x v b = b')
    (hc : subst x v c = c') : subst x v (If a b c) = If a' b' c' := by simp only [subst, ha, hb, hc]
theorem subst_pf_pair {a b a' b' : expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (Pair a b) = Pair a' b' := by simp only [subst, ha, hb]
theorem subst_pf_fst {a a' : expr} (ha : subst x v a = a') : subst x v (Fst a) = Fst a' := by
  simp only [subst, ha]
theorem subst_pf_snd {a a' : expr} (ha : subst x v a = a') : subst x v (Snd a) = Snd a' := by
  simp only [subst, ha]
theorem subst_pf_fork {a a' : expr} (ha : subst x v a = a') : subst x v (Fork a) = Fork a' := by
  simp only [subst, ha]
theorem subst_pf_prim0 (op : prim_op0) : subst x v (Primitive0 op) = Primitive0 op := rfl
theorem subst_pf_prim1 (op : prim_op1) {a a' : expr} (ha : subst x v a = a') :
    subst x v (Primitive1 op a) = Primitive1 op a' := by simp only [subst, ha]
theorem subst_pf_prim2 (op : prim_op2) {a b a' b' : expr} (ha : subst x v a = a')
    (hb : subst x v b = b') : subst x v (Primitive2 op a b) = Primitive2 op a' b' := by
  simp only [subst, ha, hb]
theorem subst_pf_extop (op : ffi_opcode) {a a' : expr} (ha : subst x v a = a') :
    subst x v (ExternalOp op a) = ExternalOp op a' := by simp only [subst, ha]
theorem subst_pf_cmpxchg {a b c a' b' c' : expr} (ha : subst x v a = a') (hb : subst x v b = b')
    (hc : subst x v c = c') : subst x v (CmpXchg a b c) = CmpXchg a' b' c' := by
  simp only [subst, ha, hb, hc]
theorem subst_pf_newproph : subst x v (NewProph : expr) = NewProph := rfl
theorem subst_pf_resolve {a b a' b' : expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (ResolveProph a b) = ResolveProph a' b' := by simp only [subst, ha, hb]

-- composite literals (`LiteralValue`): without these the kernel would evaluate
-- `subst` on the element list, deciding the `String` equality of every variable
theorem subst_pf_litval {l l' : List keyed_element} (h : subst_keyed_elements x v l = l') :
    subst x v (LiteralValue l) = LiteralValue l' := by simp only [subst, h]
theorem subst_pf_kes_nil : subst_keyed_elements x v [] = [] := by simp only [subst_keyed_elements]
theorem subst_pf_kes_cons {ke ke' : keyed_element} {l l' : List keyed_element}
    (h1 : subst_keyed_element x v ke = ke') (h2 : subst_keyed_elements x v l = l') :
    subst_keyed_elements x v (ke :: l) = ke' :: l' := by simp only [subst_keyed_elements, h1, h2]
theorem subst_pf_ke {k k' : Option key} {el el' : element} (h1 : subst_opt_key x v k = k')
    (h2 : subst_element x v el = el') :
    subst_keyed_element x v (KeyedElement k el) = KeyedElement k' el' := by
  simp only [subst_keyed_element, h1, h2]
theorem subst_pf_okey_none : subst_opt_key x v none = none := by simp only [subst_opt_key]
theorem subst_pf_okey_field (f : go_string) :
    subst_opt_key x v (some (KeyField f)) = some (KeyField f) := by simp only [subst_opt_key]
theorem subst_pf_okey_int (i : Int) :
    subst_opt_key x v (some (KeyInteger i)) = some (KeyInteger i) := by simp only [subst_opt_key]
theorem subst_pf_okey_expr (t : go.type) {e e' : expr} (h : subst x v e = e') :
    subst_opt_key x v (some (KeyExpression t e)) = some (KeyExpression t e') := by
  simp only [subst_opt_key, h]
theorem subst_pf_okey_lv {l l' : List keyed_element} (h : subst_keyed_elements x v l = l') :
    subst_opt_key x v (some (KeyLiteralValue l)) = some (KeyLiteralValue l') := by
  simp only [subst_opt_key, h]
theorem subst_pf_el_expr (t : go.type) {e e' : expr} (h : subst x v e = e') :
    subst_element x v (ElementExpression t e) = ElementExpression t e' := by
  simp only [subst_element, h]
theorem subst_pf_el_lv {l l' : List keyed_element} (h : subst_keyed_elements x v l = l') :
    subst_element x v (ElementLiteralValue l) = ElementLiteralValue l' := by
  simp only [subst_element, h]

theorem subst'_pf_anon {e e' : expr} (h : e = e') : subst' BAnon v e = e' := h
theorem subst'_pf_named {e e1 e' : expr} (h1 : e = e1) (h2 : subst x v e1 = e') :
    subst' (BNamed x) v e = e' := by rw [h1]; exact h2
theorem subst_pf_cong {e e1 e' : expr} (h1 : e = e1) (h2 : subst x v e1 = e') :
    subst x v e = e' := by rw [h1]; exact h2

end subst_pf

/-! ## Closedness annotations

`wp_auto` annotates the continuations of a long function with the set of
variables they may mention (`fvClosed S e`, definitionally `e`), so that a
substitution of a variable `x ∉ S` (typically a `let:`-bound temporary used only
in the next statement) is proved in constant size from a closedness proof of `e`
that is built once (and shared), instead of by a proof of the size of the rest of
the function at every `let:`. The annotations are removed before the goal is
returned. -/

/-- `e`, annotated with a set `S` of variables containing its free variables. -/
@[reducible] def fvClosed [ffi_syntax] (_S : List String) (e : expr) : expr := e

section closed
variable [ext : ffi_syntax]

/-- Substituting any variable not in `S` does not change `e`. -/
def ClosedUnder (S : List String) (e : expr) : Prop := ∀ x v, x ∉ S → subst x v e = e
def ClosedKEs (S : List String) (l : List keyed_element) : Prop :=
  ∀ x v, x ∉ S → subst_keyed_elements x v l = l
def ClosedKE (S : List String) (ke : keyed_element) : Prop :=
  ∀ x v, x ∉ S → subst_keyed_element x v ke = ke
def ClosedOKey (S : List String) (k : Option key) : Prop :=
  ∀ x v, x ∉ S → subst_opt_key x v k = k
def ClosedElem (S : List String) (el : element) : Prop :=
  ∀ x v, x ∉ S → subst_element x v el = el

/-- The variable names bound by binders `f`, `y`. -/
def bnames : binder → List String
  | BAnon => []
  | BNamed s => [s]

variable {S : List String}

theorem closed_val (w : val) : ClosedUnder S (Val w) := fun _ _ _ => rfl
theorem closed_var {y : String} (h : y ∈ S) : ClosedUnder S (Var y) := by
  intro x v hx; simp only [subst]; rw [if_neg]; intro e; subst e; exact hx h
theorem closed_rec {f y : binder} {e : expr} (h : ClosedUnder (bnames f ++ bnames y ++ S) e) :
    ClosedUnder S (Rec f y e) := by
  intro x v hx; simp only [subst]
  split
  · rename_i hb
    rw [h x v]
    intro hm
    simp only [List.mem_append] at hm
    rcases hm with (hm | hm) | hm
    · cases f <;> simp [bnames] at hm; subst hm; exact hb.1 rfl
    · cases y <;> simp [bnames] at hm; subst hm; exact hb.2 rfl
    · exact hx hm
  · rfl
theorem closed_app {a b : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (App a b) := by intro x v hx; simp only [subst, ha x v hx, hb x v hx]
theorem closed_if {a b c : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) (hc : ClosedUnder S c) :
    ClosedUnder S (If a b c) := by intro x v hx; simp only [subst, ha x v hx, hb x v hx, hc x v hx]
theorem closed_pair {a b : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (Pair a b) := by intro x v hx; simp only [subst, ha x v hx, hb x v hx]
theorem closed_fst {a : expr} (ha : ClosedUnder S a) : ClosedUnder S (Fst a) := by
  intro x v hx; simp only [subst, ha x v hx]
theorem closed_snd {a : expr} (ha : ClosedUnder S a) : ClosedUnder S (Snd a) := by
  intro x v hx; simp only [subst, ha x v hx]
theorem closed_fork {a : expr} (ha : ClosedUnder S a) : ClosedUnder S (Fork a) := by
  intro x v hx; simp only [subst, ha x v hx]
theorem closed_prim0 (op : prim_op0) : ClosedUnder S (Primitive0 op) := fun _ _ _ => rfl
theorem closed_prim1 (op : prim_op1) {a : expr} (ha : ClosedUnder S a) :
    ClosedUnder S (Primitive1 op a) := by intro x v hx; simp only [subst, ha x v hx]
theorem closed_prim2 (op : prim_op2) {a b : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (Primitive2 op a b) := by intro x v hx; simp only [subst, ha x v hx, hb x v hx]
theorem closed_extop (op : ffi_opcode) {a : expr} (ha : ClosedUnder S a) :
    ClosedUnder S (ExternalOp op a) := by intro x v hx; simp only [subst, ha x v hx]
theorem closed_cmpxchg {a b c : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b)
    (hc : ClosedUnder S c) : ClosedUnder S (CmpXchg a b c) := by
  intro x v hx; simp only [subst, ha x v hx, hb x v hx, hc x v hx]
theorem closed_newproph : ClosedUnder S (NewProph : expr) := fun _ _ _ => rfl
theorem closed_resolve {a b : expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (ResolveProph a b) := by intro x v hx; simp only [subst, ha x v hx, hb x v hx]
theorem closed_litval {l : List keyed_element} (h : ClosedKEs S l) : ClosedUnder S (LiteralValue l) := by
  intro x v hx; simp only [subst, h x v hx]
theorem closed_kes_nil : ClosedKEs S [] := by intro x v _; simp only [subst_keyed_elements]
theorem closed_kes_cons {ke : keyed_element} {l : List keyed_element} (h1 : ClosedKE S ke)
    (h2 : ClosedKEs S l) : ClosedKEs S (ke :: l) := by
  intro x v hx; simp only [subst_keyed_elements, h1 x v hx, h2 x v hx]
theorem closed_ke {k : Option key} {el : element} (h1 : ClosedOKey S k) (h2 : ClosedElem S el) :
    ClosedKE S (KeyedElement k el) := by
  intro x v hx; simp only [subst_keyed_element, h1 x v hx, h2 x v hx]
theorem closed_okey_none : ClosedOKey S none := by intro x v _; simp only [subst_opt_key]
theorem closed_okey_field (f : go_string) : ClosedOKey S (some (KeyField f)) := by
  intro x v _; simp only [subst_opt_key]
theorem closed_okey_int (i : Int) : ClosedOKey S (some (KeyInteger i)) := by
  intro x v _; simp only [subst_opt_key]
theorem closed_okey_expr (t : go.type) {e : expr} (h : ClosedUnder S e) :
    ClosedOKey S (some (KeyExpression t e)) := by intro x v hx; simp only [subst_opt_key, h x v hx]
theorem closed_okey_lv {l : List keyed_element} (h : ClosedKEs S l) :
    ClosedOKey S (some (KeyLiteralValue l)) := by intro x v hx; simp only [subst_opt_key, h x v hx]
theorem closed_el_expr (t : go.type) {e : expr} (h : ClosedUnder S e) :
    ClosedElem S (ElementExpression t e) := by intro x v hx; simp only [subst_element, h x v hx]
theorem closed_el_lv {l : List keyed_element} (h : ClosedKEs S l) :
    ClosedElem S (ElementLiteralValue l) := by intro x v hx; simp only [subst_element, h x v hx]
/-- A nested annotation with a smaller set. -/
theorem closed_fv {T : List String} {e : expr} (h : ClosedUnder T e) (hsub : ∀ s ∈ T, s ∈ S) :
    ClosedUnder S (fvClosed T e) := fun x v hx => h x v (fun hm => hx (hsub x hm))
theorem subset_nil : ∀ s ∈ ([] : List String), s ∈ S := by simp
theorem subset_cons {a : String} {T : List String} (h1 : a ∈ S) (h2 : ∀ s ∈ T, s ∈ S) :
    ∀ s ∈ a :: T, s ∈ S := by
  intro s hs; simp only [List.mem_cons] at hs; rcases hs with rfl | hs; exact h1; exact h2 s hs
theorem not_mem_nil' {x : String} : x ∉ ([] : List String) := by simp
theorem not_mem_cons' {x a : String} {l : List String} (h1 : x ≠ a) (h2 : x ∉ l) : x ∉ a :: l := by
  simp only [List.mem_cons, not_or]; exact ⟨h1, h2⟩

/-- The substitution of a variable `x ∉ S` into an annotated term. -/
theorem subst_pf_fvClosed {x : String} {v : val} {e : expr} (h : ClosedUnder S e) (hx : x ∉ S) :
    subst x v (fvClosed S e) = fvClosed S e := h x v hx

end closed

register_option goose.wp.extras : Bool := {
  defValue := true
  descr := "enable the extra automation of `wp_pures`/`wp_auto` (on by default): \
    the `goose_wp_simp_extra` simp set, reduction of \
    `match`es on definitions of constructors, stopping at slice composite literals, \
    and (in `wp_auto`) storing function literals and unfolding package constants"
}

register_option goose.wp.unfoldSliceLiterals : Bool := {
  defValue := false
  descr := "let `wp_pures`/`wp_auto` step slice composite literals \
    (`go.SliceSemantics.composite_literal_slice`) instead of stopping at them \
    (use `wp_slice_literal`, as in Rocq)"
}

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
  let mut raw : Std.HashMap Nat Expr := {}
  for (n, v) in unchecked do
    let n := (n.drop 1).toString
    let some i := names.idxOf? (Name.mkSimple n) | throwError "mkAppNamed: {c} has no argument {n}"
    mvs[i]!.mvarId!.assign v
    raw := raw.insert i v
  -- unchecked arguments (typically large sub-proofs) are used as given, without
  -- `instantiateMVars`: instantiating them at every step made the tactics quadratic
  let mut out := #[]
  for i in [:mvs.size] do
    if let some v := raw[i]? then
      out := out.push v
    else
      unless ← mvs[i]!.mvarId!.isAssigned do
        throwError "mkAppNamed: argument {names[i]!} of {c} could not be inferred"
      out := out.push (← instantiateMVars mvs[i]!)
  let us ← us.mapM instantiateLevelMVars
  return mkAppN (mkConst c us) out

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

/-- Caches of `needsGooseSimp` (cleared by `wp_auto`/`wp_pures` at the start):
the simp heads, the result per (shared) subterm, and per constant. -/
initialize needsHeadsCache : IO.Ref (Option (Option NameSet)) ← IO.mkRef none
initialize needsCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}
initialize needsConstCache : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

/-- Clear the caches of `needsGooseSimp`. -/
def clearNeedsCaches : BaseIO Unit := do
  needsHeadsCache.set none; needsCache.set {}; needsConstCache.set {}

/-- Run the tactic `k` on the main goal with elaboration errors raised as
exceptions (`Term.withoutErrToSorry`, no error recovery), and fail if the proof
it produces contains a (synthetic) `sorry` that was not already in the goal.
All GooseLang WP tactics run under this guard, so that e.g. an ill-typed lemma
given to `wp_apply` is an error rather than a silently admitted goal. -/
def withNoSorry {α} (tacName : Name) (k : TacticM α) : TacticM α := do
  let mvar ← getMainGoal
  let hadSorry := (← instantiateMVars (← mvar.getType)).hasSyntheticSorry
  let r ← Term.withoutErrToSorry <| withoutRecover k
  unless hadSorry do
    if (← instantiateMVars (mkMVar mvar)).hasSyntheticSorry then
      throwError "{tacName}: elaboration failed (the proof would contain `sorry`)"
  return r

/-- Run `k` on the current Iris goal, which must be a GooseLang WP (under
`withNoSorry`). -/
def runTacticGooseWp {α} (tacName : Name)
    (k : MVarId → IrisGoal → GooseWpGoal → ProofModeM α) : TacticM α :=
  withNoSorry tacName <| ProofModeM.runTactic tacName fun mvar g => do
    clearNeedsCaches
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

/-- The simp sets used to normalize WP expressions: `goose_wp_simp`, and
`goose_wp_simp_extra` with `goose.wp.extras`. -/
def gooseSimpSets (opts : Options) : List Name :=
  if goose.wp.extras.get opts then [`goose_wp_simp, `goose_wp_simp_extra] else [`goose_wp_simp]

/-- Reduce the `match`es of `e` whose discriminants reduce to constructors with
default transparency (e.g. `match interface.nil with ...` after `cases`, where
`interface.nil` is a definition); `simp`'s `iota` only unfolds reducible
definitions. The result is definitionally equal to `e`. -/
def reduceMatchersDefault (e : Expr) : MetaM Expr := do
  unless goose.wp.extras.get (← getOptions) do return e
  let env ← getEnv
  unless (e.find? fun s => match s with
      | .const n _ => (isMatcherCore env n).or ((n == ``ZeroVal.zero_val_def).or
          ((env.getProjectionFnInfo? n).any (!·.fromClass)))
      | _ => false).isSome do return e
  Meta.transform e (post := fun s => do
    let .const n _ := s.getAppFn | return .continue
    -- a projection of a definition of a constructor application, e.g.
    -- `(zero_val S.t).f'` or `(interface.mk t v).v`
    if let some info := env.getProjectionFnInfo? n then
      -- `zero_val V` of a base type (`W64 0`, `false`, `slice.nil`, ...); the
      -- zero value of a struct stays folded
      if n == ``ZeroVal.zero_val_def then
        let args := s.getAppArgs
        if h : 1 < args.size then
          let inst ← withTransparency .default (whnf args[1])
          if let some ctor := inst.getAppFn.constName? then
            if let some (.ctorInfo ci) := env.find? ctor then
              if ci.numParams < inst.getAppNumArgs then
                let z := inst.getAppArgs[ci.numParams]!
                let zh ← whnfR z
                let isStructCtor := match zh.getAppFn.constName? >>= env.find? with
                  | some (.ctorInfo zi) => isStructure env zi.induct
                  | _ => false
                unless isStructCtor || z.hasLooseBVars do
                  return .visit (mkAppN z (args.extract 2 args.size))
        return .continue
      -- not class projections (`LT.lt`, ...): those are notation
      if info.fromClass then return .continue
      let args := s.getAppArgs
      if h : info.numParams < args.size then
        let st := args[info.numParams]
        if st.getAppFn.isConst && !(env.find? st.getAppFn.constName!).any (·.isCtor) then
          let st' ← withTransparency .default (whnf st)
          if ← isConstructorApp st' then
            let some ctor := st'.getAppFn.constName? | return .continue
            let some (.ctorInfo ci) := env.find? ctor | return .continue
            let fields := st'.getAppArgs.extract ci.numParams st'.getAppNumArgs
            if h' : info.i < fields.size then
              return .visit (mkAppN fields[info.i] (args.extract (info.numParams + 1) args.size)).headBeta
      return .continue
    unless isMatcherCore env n do return .continue
    let some app ← matchMatcherApp? s | return .continue
    -- only when every discriminant unfolds to a constructor (no structure eta)
    for d in app.discrs do
      let d ← withTransparency .default (whnf d)
      unless (← isConstructorApp d) || d.isLit do return .continue
    match ← withTransparency .default (reduceMatcher? s) with
    | .reduced s' => return .visit s'.headBeta
    | _ => return .continue)

/-- Simplify a GooseLang expression with the `goose_wp_simp` simp set, returning
the new expression and a proof of `e = e'` (or `none` if unchanged). `match`es
on (definitions of) constructors are reduced first (`reduceMatchersDefault`). -/
def gooseExprSimp (e : Expr) : MetaM (Expr × Option Expr) := do
  let e0 := e
  let e ← reduceMatchersDefault e
  let p0? ← if e == e0 then pure none
    else some <$> mkExpectedTypeHint (← mkEqRefl e0) (← mkEq e0 e)
  let (e', p?) ← gooseExprSimpCore e
  match p0?, p? with
  | none, _ => return (e', p?)
  | some p0, none => return (e', some p0)
  | some p0, some p => return (e', some (← mkEqTrans p0 p))
where
  gooseExprSimpCore (e : Expr) : MetaM (Expr × Option Expr) := do
  let mut theorems := #[]
  let mut procs := #[]
  for attr in gooseSimpSets (← getOptions) do
    let some ext ← getSimpExtension? attr
      | throwError "cannot find the `{attr}` simp set"
    let some procext ← Simp.getSimprocExtension? attr
      | throwError "cannot find the `{attr}` simprocs"
    theorems := theorems.push (← ext.getTheorems)
    procs := procs.push (← procext.getSimprocs)
  let ctx ← Simp.mkContext (simpTheorems := theorems) (congrTheorems := ← getSimpCongrTheorems)
    (config := { beta := true, eta := true, zeta := true, proj := true, iota := true,
                 decide := false })
  let ⟨res, _⟩ ← Meta.simp e ctx (simprocs := procs)
  return (res.expr, res.proof?)


/-- Head constants that some `goose_wp_simp` rule (theorem, unfolding or simproc)
could rewrite, or `none` if some rule is not keyed by a constant. -/
def gooseSimpHeads : MetaM (Option NameSet) := do
  let mut s : NameSet := {}
  for attr in gooseSimpSets (← getOptions) do
    let some ext ← getSimpExtension? attr | return none
    let some procext ← Simp.getSimprocExtension? attr | return none
    let th ← ext.getTheorems
    let ps ← procext.getSimprocs
    for n in th.toUnfold.toList do s := s.insert n
    let keys := th.pre.root.toList.map (·.1) ++ th.post.root.toList.map (·.1) ++
      ps.pre.root.toList.map (·.1) ++ ps.post.root.toList.map (·.1)
    for k in keys do
      match k with
      | .const n _ => s := s.insert n
      | _ => return none
  return some s

/-- Could `gooseExprSimp` change `e`? A conservative syntactic check (some
subterm is headed by a constant that a `goose_wp_simp` rule rewrites, a
matcher/recursor, a projection of a constructor, a `let`, or a beta-redex), so
that the (expensive) simp call over the whole expression is skipped when it
would do nothing. -/
def needsGooseSimp (e : Expr) : MetaM Bool := do
  let heads? ← match ← needsHeadsCache.get with
    | some h => pure h
    | none => do let h ← gooseSimpHeads; needsHeadsCache.set (some h); pure h
  let some heads := heads? | return true
  let env ← getEnv
  let extras := goose.wp.extras.get (← getOptions)
  -- a constant some rule applies to; for a reducible definition (`sint.Z`, `W64`,
  -- seen through by simp's discrimination trees), the head of its unfolding
  let constNeeds (n : Name) : MetaM Bool := do
    if let some b := (← needsConstCache.get)[n]? then return b
    let b ← do
      if (heads.contains n).or ((isMatcherCore env n).or ((isAuxRecursor env n).or (isRecCore env n))) then
        pure true
      else if extras.and ((← getReducibilityStatus n) == .reducible) then
        match (env.find? n).bind (·.value?) with
        | some v =>
          let rec body : Expr → Expr
            | .lam _ _ b _ => body b
            | b => b
          pure ((body v).getAppFn.constName?.any heads.contains)
        | none => pure false
      else pure false
    needsConstCache.modify (·.insert n b)
    return b
  let localNeeds (s : Expr) : MetaM Bool := do
    match s with
    | .const n _ => constNeeds n
    | .proj .. | .letE .. => return true
    | .app .. =>
      if s.isHeadBetaTarget then return true
      match s.getAppFn with
      | .const n _ => match env.getProjectionFnInfo? n with
        | some info =>
          let args := s.getAppArgs
          if h : info.numParams < args.size then
            match args[info.numParams].getAppFn with
            | .const c _ =>
              let b1 := extras.and ((!info.fromClass).or (n == ``ZeroVal.zero_val_def))
              return b1.or ((env.find? c).any (·.isCtor))
            | _ => return false
          else return false
        | none => return false
      | _ => return false
    | _ => return false
  let rec go (s : Expr) : MetaM Bool := do
    if let some b := (← needsCache.get)[s]? then return b
    let b ← do
      if ← localNeeds s then pure true
      else match s with
        | .app f a => do if ← go f then pure true else go a
        | .lam _ t b _ | .forallE _ t b _ => do if ← go t then pure true else go b
        | .mdata _ b => go b
        | _ => pure false
    needsCache.modify (·.insert s b)
    return b
  go e

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

/-- A proof of `ae ≠ be` for distinct string literals `a`, `b` (`ae`, `be` reduce to them),
cheap to check for the kernel (no UTF-8 encoding). -/
def strNeProof (a b : String) (ae be : Expr) : Expr :=
  let rec go (cs ds : List Char) : Expr × Expr × Expr :=
    -- returns (cs expr, ds expr, proof cs ≠ ds)
    let charE (c : Char) := mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)
    let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``Char)
    let cons (c t : Expr) := mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) c t
    let lit (l : List Char) := l.foldr (fun c acc => cons (charE c) acc) nil
    match cs, ds with
    | [], d :: ds' => (nil, lit (d :: ds'), mkApp2 (mkConst ``list_char_ne_nil_cons) (charE d) (lit ds'))
    | c :: cs', [] => (lit (c :: cs'), nil, mkApp2 (mkConst ``list_char_ne_cons_nil) (charE c) (lit cs'))
    | c :: cs', d :: ds' =>
      if c == d then
        let (ce, de, p) := go cs' ds'
        (cons (charE c) ce, cons (charE c) de, mkApp4 (mkConst ``list_char_ne_tail) (charE c) ce de p)
      else
        let hne := mkApp3 (mkConst ``Nat.ne_of_beq_eq_false) (mkApp (mkConst ``Char.toNat) (charE c))
          (mkApp (mkConst ``Char.toNat) (charE d))
          (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.false))
        (lit (c :: cs'), lit (d :: ds'),
          mkApp5 (mkConst ``list_char_ne_head) (charE c) (charE d) (lit cs') (lit ds') hne)
    | [], [] => (nil, nil, mkConst ``True.intro) -- unreachable
  let (ce, de, p) := go a.toList b.toList
  let strTy := mkConst ``String
  let hs := mkApp2 (mkConst ``Eq.refl [1]) strTy ae
  let ht := mkApp2 (mkConst ``Eq.refl [1]) strTy be
  mkAppN (mkConst ``str_ne_of_list_ne) #[ae, be, ce, de, hs, ht, p]

/-- A proof of `BNamed x ≠ b` for a binder literal `b` different from `BNamed x`. -/
def binderNeProof (ext : Expr) (x : String) (xe : Expr) (b : Option String) (be : Expr) : Expr :=
  match b with
  | none => mkApp2 (mkConst ``binder_named_ne_anon) ext xe
  | some y =>
    let ye := (be.getArg! 0)
    mkApp4 (mkConst ``binder_named_ne_named) ext xe ye (strNeProof x y xe ye)

/-- Whether `wp_auto` takes `if: #(decide P) then e else AngelicExit #()` steps
(introducing `P` as an inaccessible hypothesis); set by
`solve_into_val_typed_struct` (`Auto.lean`). -/
initialize autoAngelicIf : IO.Ref Bool ← IO.mkRef false

register_option goose.wp.fvAnnot : Bool := {
  defValue := true
  descr := "let `wp_auto` annotate continuations with their free variables, so that \
    substitutions into the rest of a long function are proved in constant size"
}

/-! ### Closedness annotations (meta level) -/

/-- Whether `substPf` uses closedness annotations (`fvClosed`), and the caches of
free-variable sets and closedness proofs (set up by `wp_auto`). -/
initialize fvAnnotMode : IO.Ref Bool ← IO.mkRef false
initialize fvCache : IO.Ref (Std.HashMap Expr (Option (List String))) ← IO.mkRef {}
initialize closedCache : IO.Ref (Std.HashMap (Expr × Expr) (Option Expr)) ← IO.mkRef {}

/-- A literal `List String` expression. -/
def strListExpr (l : List String) : Expr :=
  let ty := mkConst ``String
  l.foldr (fun s acc => mkApp3 (mkConst ``List.cons [0]) ty (mkStrLit s) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- Parse a literal `List String` expression. -/
partial def strList? (e : Expr) : MetaM (Option (List String)) := do
  let e ← whnfR e
  if e.isAppOfArity ``List.nil 1 then return some []
  unless e.isAppOfArity ``List.cons 3 do return none
  let some s ← strLit? (e.getArg! 1) | return none
  let some t ← strList? (e.getArg! 2) | return none
  return some (s :: t)

/-- A proof of `s ∈ l` for a literal list `l` (as `le`) containing `s`. -/
def memPf (s : String) (l : List String) (le : Expr) : MetaM (Option Expr) := do
  match l with
  | [] => return none
  | a :: t =>
    let le ← whnfR le
    let tl := le.getArg! 2
    if a == s then
      return some (mkApp3 (mkConst ``List.Mem.head [0]) (mkConst ``String) (mkStrLit s) tl)
    let some p ← memPf s t tl | return none
    return some (mkApp5 (mkConst ``List.Mem.tail [0]) (mkConst ``String) (mkStrLit s) (mkStrLit a) tl p)

/-- A proof of `x ∉ l` for a literal list `l` not containing `x`. -/
def notMemPf (ext : Expr) (x : String) (xe : Expr) (l : List String) : Expr :=
  match l with
  | [] => mkApp2 (mkConst ``not_mem_nil') ext xe
  | a :: t =>
    let ae := mkStrLit a
    mkApp6 (mkConst ``not_mem_cons') ext xe ae (strListExpr t) (strNeProof x a xe ae)
      (notMemPf ext x xe t)

/-- The free variables of an `expr` built from constructors (`none` if some part
is not), using the annotations `fvClosed S e` (whose set is `S`). -/
partial def fvOf (e : Expr) : MetaM (Option (List String)) := do
  if let some r := (← fvCache.get)[e]? then return r
  let union (a b : List String) : List String := a ++ b.filter (!a.contains ·)
  let r ← do
    if e.isAppOfArity ``fvClosed 3 then strList? (e.getArg! 1) else
    let e ← whnfR e
    let args := e.getAppArgs
    let all (xs : List Expr) : MetaM (Option (List String)) := do
      let mut acc := []
      for x in xs do
        let some f ← fvOf x | return none
        acc := union acc f
      return some acc
    match e.getAppFn.constName? with
    | some ``Perennial.expr.Val => pure (some [])
    | some ``Perennial.expr.Var => pure ((← strLit? args[1]!).map ([·]))
    | some ``Perennial.expr.Rec =>
      match ← binderLit? args[1]!, ← binderLit? args[2]!, ← fvOf args[3]! with
      | some f, some y, some b => pure (some (b.filter fun s => some s != f && some s != y))
      | _, _, _ => pure none
    | some ``Perennial.expr.App => all [args[1]!, args[2]!]
    | some ``Perennial.expr.If => all [args[1]!, args[2]!, args[3]!]
    | some ``Perennial.expr.Pair => all [args[1]!, args[2]!]
    | some ``Perennial.expr.Fst => all [args[1]!]
    | some ``Perennial.expr.Snd => all [args[1]!]
    | some ``Perennial.expr.Fork => all [args[1]!]
    | some ``Perennial.expr.Primitive0 => pure (some [])
    | some ``Perennial.expr.Primitive1 => all [args[2]!]
    | some ``Perennial.expr.Primitive2 => all [args[2]!, args[3]!]
    | some ``Perennial.expr.ExternalOp => all [args[2]!]
    | some ``Perennial.expr.CmpXchg => all [args[1]!, args[2]!, args[3]!]
    | some ``Perennial.expr.NewProph => pure (some [])
    | some ``Perennial.expr.ResolveProph => all [args[1]!, args[2]!]
    -- composite literals (possibly long, e.g. lookup tables) are not annotated
    | some ``Perennial.expr.LiteralValue => pure none
    | _ => pure none
  fvCache.modify (·.insert e r)
  return r
where
  fvKEs (l : Expr) : MetaM (Option (List String)) := do
    let l ← whnfR l
    if l.isAppOfArity ``List.nil 1 then return some []
    unless l.isAppOfArity ``List.cons 3 do return none
    let ke ← whnfR (l.getArg! 1)
    unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
    let some a ← fvKey (ke.getArg! 1) | return none
    let some b ← fvElem (ke.getArg! 2) | return none
    let some c ← fvKEs (l.getArg! 2) | return none
    return some (a ++ b ++ c)
  fvKey (k : Expr) : MetaM (Option (List String)) := do
    let k ← whnfR k
    if k.isAppOfArity ``Option.none 1 then return some []
    unless k.isAppOfArity ``Option.some 2 do return none
    let kk ← whnfR (k.getArg! 1)
    match kk.getAppFn.constName? with
    | some ``Perennial.key.KeyField => return some []
    | some ``Perennial.key.KeyInteger => return some []
    | some ``Perennial.key.KeyExpression => fvOf (kk.getArg! 2)
    | some ``Perennial.key.KeyLiteralValue => fvKEs (kk.getArg! 1)
    | _ => return none
  fvElem (el : Expr) : MetaM (Option (List String)) := do
    let el ← whnfR el
    match el.getAppFn.constName? with
    | some ``Perennial.element.ElementExpression => fvOf (el.getArg! 2)
    | some ``Perennial.element.ElementLiteralValue => fvKEs (el.getArg! 1)
    | _ => return none

/-- A proof of `ClosedUnder S e` (`S` given as the literal `Se`), built from the
constructors of `e`; `none` if it cannot be built. Cached on `(Se, e)`. -/
partial def closedPf (ext : Expr) (S : List String) (Se : Expr) (e : Expr) : MetaM (Option Expr) := do
  if let some r := (← closedCache.get)[(Se, e)]? then return r
  let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
  let r ← do
    if e.isAppOfArity ``fvClosed 3 then
      -- a nested annotation: its own proof, and the inclusion of its set
      let Te := e.getArg! 1; let b := e.getArg! 2
      let some T ← strList? Te | pure none
      let some hb ← closedPf ext T Te b | pure none
      let some hsub ← subsetPf T Te | pure none
      pure (some (lem ``closed_fv #[Te, b, hb, hsub]))
    else
    let e ← whnfR e
    let args := e.getAppArgs
    let rec' (x : Expr) := closedPf ext S Se x
    match e.getAppFn.constName? with
    | some ``Perennial.expr.Val => pure (some (lem ``closed_val #[args[1]!]))
    | some ``Perennial.expr.Var =>
      match ← strLit? args[1]! with
      | some y => match ← memPf y S Se with
        | some h => pure (some (lem ``closed_var #[args[1]!, h]))
        | none => pure none
      | none => pure none
    | some ``Perennial.expr.Rec =>
      let f ← whnfR args[1]!; let y ← whnfR args[2]!
      match ← binderLit? f, ← binderLit? y with
      | some fb, some yb =>
        let T := fb.toList ++ yb.toList ++ S
        let Te := strListExpr T
        match ← closedPf ext T Te args[3]! with
        | some hb =>
          -- `ClosedUnder (bnames f ++ bnames y ++ S) b` is `ClosedUnder T b` by `rfl`
          let ty ← mkAppM ``ClosedUnder #[← mkAppM ``HAppend.hAppend
            #[← mkAppM ``HAppend.hAppend #[mkApp (mkConst ``bnames) f, mkApp (mkConst ``bnames) y], Se],
            args[3]!]
          pure (some (lem ``closed_rec #[f, y, args[3]!, ← mkExpectedTypeHint hb ty]))
        | none => pure none
      | _, _ => pure none
    | some ``Perennial.expr.App =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_app #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.expr.If =>
      match ← rec' args[1]!, ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb, some hc =>
        pure (some (lem ``closed_if #[args[1]!, args[2]!, args[3]!, ha, hb, hc]))
      | _, _, _ => pure none
    | some ``Perennial.expr.Pair =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_pair #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.expr.Fst => return (← rec' args[1]!).map (lem ``closed_fst #[args[1]!, ·])
    | some ``Perennial.expr.Snd => return (← rec' args[1]!).map (lem ``closed_snd #[args[1]!, ·])
    | some ``Perennial.expr.Fork => return (← rec' args[1]!).map (lem ``closed_fork #[args[1]!, ·])
    | some ``Perennial.expr.Primitive0 => pure (some (lem ``closed_prim0 #[args[1]!]))
    | some ``Perennial.expr.Primitive1 =>
      return (← rec' args[2]!).map (lem ``closed_prim1 #[args[1]!, args[2]!, ·])
    | some ``Perennial.expr.Primitive2 =>
      match ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb => pure (some (lem ``closed_prim2 #[args[1]!, args[2]!, args[3]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.expr.ExternalOp =>
      return (← rec' args[2]!).map (lem ``closed_extop #[args[1]!, args[2]!, ·])
    | some ``Perennial.expr.CmpXchg =>
      match ← rec' args[1]!, ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb, some hc =>
        pure (some (lem ``closed_cmpxchg #[args[1]!, args[2]!, args[3]!, ha, hb, hc]))
      | _, _, _ => pure none
    | some ``Perennial.expr.NewProph => pure (some (lem ``closed_newproph #[]))
    | some ``Perennial.expr.ResolveProph =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_resolve #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.expr.LiteralValue =>
      return (← closedKEs args[1]!).map (lem ``closed_litval #[args[1]!, ·])
    | _ => pure none
  closedCache.modify (·.insert (Se, e) r)
  return r
where
  subsetPf (T : List String) (Te : Expr) : MetaM (Option Expr) := do
    match T with
    | [] => return some (mkApp2 (mkConst ``subset_nil) ext Se)
    | a :: t =>
      let Te' ← whnfR Te
      let tl := Te'.getArg! 2
      let some h1 ← memPf a S Se | return none
      let some h2 ← subsetPf t tl | return none
      return some (mkAppN (mkConst ``subset_cons) #[ext, Se, mkStrLit a, tl, h1, h2])
  closedKEs (l : Expr) : MetaM (Option Expr) := do
    let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
    let l ← whnfR l
    if l.isAppOfArity ``List.nil 1 then return some (lem ``closed_kes_nil #[])
    unless l.isAppOfArity ``List.cons 3 do return none
    let ke ← whnfR (l.getArg! 1)
    unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
    let k := ke.getArg! 1; let el := ke.getArg! 2
    let some hk ← closedKey k | return none
    let some he ← closedElem el | return none
    let some ht ← closedKEs (l.getArg! 2) | return none
    let hke := lem ``closed_ke #[k, el, hk, he]
    return some (lem ``closed_kes_cons #[ke, l.getArg! 2, hke, ht])
  closedKey (k : Expr) : MetaM (Option Expr) := do
    let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
    let k ← whnfR k
    if k.isAppOfArity ``Option.none 1 then return some (lem ``closed_okey_none #[])
    unless k.isAppOfArity ``Option.some 2 do return none
    let kk ← whnfR (k.getArg! 1)
    match kk.getAppFn.constName? with
    | some ``Perennial.key.KeyField => return some (lem ``closed_okey_field #[kk.getArg! 1])
    | some ``Perennial.key.KeyInteger => return some (lem ``closed_okey_int #[kk.getArg! 1])
    | some ``Perennial.key.KeyExpression =>
      return (← closedPf ext S Se (kk.getArg! 2)).map (lem ``closed_okey_expr #[kk.getArg! 1, kk.getArg! 2, ·])
    | some ``Perennial.key.KeyLiteralValue =>
      return (← closedKEs (kk.getArg! 1)).map (lem ``closed_okey_lv #[kk.getArg! 1, ·])
    | _ => return none
  closedElem (el : Expr) : MetaM (Option Expr) := do
    let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
    let el ← whnfR el
    match el.getAppFn.constName? with
    | some ``Perennial.element.ElementExpression =>
      return (← closedPf ext S Se (el.getArg! 2)).map (lem ``closed_el_expr #[el.getArg! 1, el.getArg! 2, ·])
    | some ``Perennial.element.ElementLiteralValue =>
      return (← closedKEs (el.getArg! 1)).map (lem ``closed_el_lv #[el.getArg! 1, ·])
    | _ => return none

mutual

/-- `subst x v e` with a proof `subst x v e = e'` built from per-constructor lemmas
(non-constructor subterms are left as `subst x v _`, proved by `rfl`). -/
partial def substPf (ext : Expr) (x : String) (xe v : Expr) (dirty : IO.Ref Bool) (e : Expr) :
    MetaM (Expr × Expr) := do
  -- a closedness annotation `fvClosed S b`
  if e.isAppOfArity ``fvClosed 3 then
    let Se := e.getArg! 1; let b := e.getArg! 2
    if let some S ← strList? Se then
      if !S.contains x then
        if let some h ← closedPf ext S Se b then
          return (e, mkAppN (mkConst ``subst_pf_fvClosed) #[ext, Se, xe, v, b, h, notMemPf ext x xe S])
      -- `x` may occur: substitute into the body (definitionally the same), keeping
      -- the annotation with `x` removed
      let (b', pb) ← substPf ext x xe v dirty b
      let S' := S.filter (· != x)
      return (mkApp3 (mkConst ``fvClosed) ext (strListExpr S') b', pb)
  let e ← whnfR e
  let substE (e : Expr) := mkApp4 (mkConst ``Perennial.subst) ext xe v e
  let fallback : MetaM (Expr × Expr) := do
    dirty.set true
    let s := substE e
    return (s, ← mkEqRefl s)
  let rec' := substPf ext x xe v dirty
  let mk (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Perennial.expr.Val, #[_, w] => return (e, lem ``subst_pf_val #[w])
  | some ``Perennial.expr.Var, #[_, y] =>
    match ← strLit? y with
    | some y' =>
      if y' == x then return (mk ``Perennial.expr.Val #[v], lem ``subst_pf_var_eq #[])
      else return (e, lem ``subst_pf_var_ne #[y, strNeProof x y' xe y])
    | none => fallback
  | some ``Perennial.expr.Rec, #[_, f, y, body] =>
    match ← binderLit? f, ← binderLit? y with
    | some fb, some yb =>
      if fb == some x then return (e, lem ``subst_pf_rec_f #[y, body])
      if yb == some x then return (e, lem ``subst_pf_rec_y #[f, body])
      let (body', pb) ← rec' body
      let f ← whnfR f; let y ← whnfR y
      let hf := binderNeProof ext x xe fb f
      let hy := binderNeProof ext x xe yb y
      return (mk ``Perennial.expr.Rec #[f, y, body'], lem ``subst_pf_rec #[f, y, body, body', hf, hy, pb])
    | _, _ => fallback
  | some ``Perennial.expr.App, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.expr.App #[a', b'], lem ``subst_pf_app #[a, b, a', b', pa, pb])
  | some ``Perennial.expr.If, #[_, a, b, c] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b; let (c', pc) ← rec' c
    return (mk ``Perennial.expr.If #[a', b', c'], lem ``subst_pf_if #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.expr.Pair, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.expr.Pair #[a', b'], lem ``subst_pf_pair #[a, b, a', b', pa, pb])
  | some ``Perennial.expr.Fst, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.expr.Fst #[a'], lem ``subst_pf_fst #[a, a', pa])
  | some ``Perennial.expr.Snd, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.expr.Snd #[a'], lem ``subst_pf_snd #[a, a', pa])
  | some ``Perennial.expr.Fork, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.expr.Fork #[a'], lem ``subst_pf_fork #[a, a', pa])
  | some ``Perennial.expr.Primitive0, #[_, op] => return (e, lem ``subst_pf_prim0 #[op])
  | some ``Perennial.expr.Primitive1, #[_, op, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.expr.Primitive1 #[op, a'], lem ``subst_pf_prim1 #[op, a, a', pa])
  | some ``Perennial.expr.Primitive2, #[_, op, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.expr.Primitive2 #[op, a', b'], lem ``subst_pf_prim2 #[op, a, b, a', b', pa, pb])
  | some ``Perennial.expr.ExternalOp, #[_, op, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.expr.ExternalOp #[op, a'], lem ``subst_pf_extop #[op, a, a', pa])
  | some ``Perennial.expr.CmpXchg, #[_, a, b, c] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b; let (c', pc) ← rec' c
    return (mk ``Perennial.expr.CmpXchg #[a', b', c'], lem ``subst_pf_cmpxchg #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.expr.NewProph, #[_] => return (e, lem ``subst_pf_newproph #[])
  | some ``Perennial.expr.ResolveProph, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.expr.ResolveProph #[a', b'], lem ``subst_pf_resolve #[a, b, a', b', pa, pb])
  | some ``Perennial.expr.LiteralValue, #[_, l] =>
    match ← substKEsPf ext x xe v dirty l with
    | some (l', pl) =>
      return (mk ``Perennial.expr.LiteralValue #[l'], lem ``subst_pf_litval #[l, l', pl])
    | none => fallback
  | _, _ => fallback

/-- `subst_keyed_elements x v l` with a proof, for a list `l` built from constructors
(`none` otherwise). -/
partial def substKEsPf (ext : Expr) (x : String) (xe v : Expr) (dirty : IO.Ref Bool) (l : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  let l ← whnfR l
  if l.isAppOfArity ``List.nil 1 then return some (l, lem ``subst_pf_kes_nil #[])
  unless l.isAppOfArity ``List.cons 3 do return none
  let ke := l.getArg! 1; let tl := l.getArg! 2
  let some (ke', p1) ← substKEPf ext x xe v dirty ke | return none
  let some (tl', p2) ← substKEsPf ext x xe v dirty tl | return none
  return some (mkApp3 (mkConst ``List.cons [0]) (l.getArg! 0) ke' tl',
    lem ``subst_pf_kes_cons #[ke, ke', tl, tl', p1, p2])

/-- `subst_keyed_element x v ke` with a proof (see `substKEsPf`). -/
partial def substKEPf (ext : Expr) (x : String) (xe v : Expr) (dirty : IO.Ref Bool) (ke : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let lem (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  let mk (n : Name) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let ke ← whnfR ke
  unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
  let k ← whnfR (ke.getArg! 1)
  let el ← whnfR (ke.getArg! 2)
  let key? : MetaM (Option (Expr × Expr)) := do
    if k.isAppOfArity ``Option.none 1 then return some (k, lem ``subst_pf_okey_none #[])
    unless k.isAppOfArity ``Option.some 2 do return none
    let kk ← whnfR (k.getArg! 1)
    let some' (e : Expr) := mkApp2 (mkConst ``Option.some [0]) (k.getArg! 0) e
    match kk.getAppFn.constName?, kk.getAppArgs with
    | some ``Perennial.key.KeyField, #[_, f] => return some (k, lem ``subst_pf_okey_field #[f])
    | some ``Perennial.key.KeyInteger, #[_, i] => return some (k, lem ``subst_pf_okey_int #[i])
    | some ``Perennial.key.KeyExpression, #[_, t, e] =>
      let (e', pe) ← substPf ext x xe v dirty e
      return some (some' (mk ``Perennial.key.KeyExpression #[t, e']),
        lem ``subst_pf_okey_expr #[t, e, e', pe])
    | some ``Perennial.key.KeyLiteralValue, #[_, l] =>
      let some (l', pl) ← substKEsPf ext x xe v dirty l | return none
      return some (some' (mk ``Perennial.key.KeyLiteralValue #[l']),
        lem ``subst_pf_okey_lv #[l, l', pl])
    | _, _ => return none
  let elem? : MetaM (Option (Expr × Expr)) := do
    match el.getAppFn.constName?, el.getAppArgs with
    | some ``Perennial.element.ElementExpression, #[_, t, e] =>
      let (e', pe) ← substPf ext x xe v dirty e
      return some (mk ``Perennial.element.ElementExpression #[t, e'],
        lem ``subst_pf_el_expr #[t, e, e', pe])
    | some ``Perennial.element.ElementLiteralValue, #[_, l] =>
      let some (l', pl) ← substKEsPf ext x xe v dirty l | return none
      return some (mk ``Perennial.element.ElementLiteralValue #[l'],
        lem ``subst_pf_el_lv #[l, l', pl])
    | _, _ => return none
  let some (k', p1) ← key? | return none
  let some (el', p2) ← elem? | return none
  return some (mk ``Perennial.keyed_element.KeyedElement #[k', el'],
    lem ``subst_pf_ke #[k, k', el, el', p1, p2])

end

/-- Annotate the continuations (bodies of `let:`/`;;` lambdas and of the
`exception_seq` continuation) of a large expression with their free variables
(`fvClosed`); the result is definitionally equal to `e`. -/
partial def annotateFv (ext : Expr) (e : Expr) : MetaM Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap Expr Expr)
  go cache e
where
  wrapRec (cache : IO.Ref (Std.HashMap Expr Expr)) (r : Expr) : MetaM Expr := do
    let r' ← whnfR r
    let_expr Perennial.expr.Rec _ f y body := r' | go cache r
    let body' ← go cache body
    -- small bodies are not worth it, and very deep ones (e.g. long composite
    -- literals) would make the closedness proofs too deep
    if decide (body'.approxDepth.toNat < 6) then
      return mkApp4 (mkConst ``Perennial.expr.Rec) ext f y body'
    match ← fvOf body' with
    | some S =>
      return mkApp4 (mkConst ``Perennial.expr.Rec) ext f y
        (mkApp3 (mkConst ``fvClosed) ext (strListExpr S) body')
    | none => return mkApp4 (mkConst ``Perennial.expr.Rec) ext f y body'
  go (cache : IO.Ref (Std.HashMap Expr Expr)) (e : Expr) : MetaM Expr := do
    if let some r := (← cache.get)[e]? then return r
    let e' ← whnfR e
    let r ← match_expr e' with
      | Perennial.expr.App _ a b => do
        let a' ← whnfR a
        let isSeq := match_expr a' with
          | Perennial.expr.Val _ c => c.getAppFn.isConstOf ``exception_seq
          | _ => false
        let isRec := a'.isAppOf ``Perennial.expr.Rec
        let na ← if isRec then wrapRec cache a else go cache a
        let nb ← if isSeq && (← whnfR b).isAppOf ``Perennial.expr.Rec then wrapRec cache b
          else go cache b
        pure (mkApp3 (mkConst ``Perennial.expr.App) ext na nb)
      | Perennial.expr.If _ a b c => do
        pure (mkApp4 (mkConst ``Perennial.expr.If) ext (← go cache a) (← go cache b) (← go cache c))
      | Perennial.expr.Pair _ a b => do
        pure (mkApp3 (mkConst ``Perennial.expr.Pair) ext (← go cache a) (← go cache b))
      | _ => pure e
    cache.modify (·.insert e r)
    return r

/-- Remove the closedness annotations (definitionally). -/
partial def stripFvCore (e : Expr) : Expr :=
  e.replace fun s => if s.isAppOfArity ``fvClosed 3 then some (stripFvCore (s.getArg! 2)) else none

def stripFv (e : Expr) : Expr :=
  if (e.find? (·.isConstOf ``fvClosed)).isNone then e else stripFvCore e

theorem tac_goal_defeq {PROP : Type _} [BI PROP] {Δ P Q : PROP} (h : Δ ⊢ Q) (heq : P = Q) : Δ ⊢ P :=
  heq ▸ h

/-- Add the goal `hyps ⊢ goal` with the closedness annotations removed. -/
def addBIGoalStripped {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Q($prop)) (k : Q($prop) → ProofModeM Expr := addBIGoal hyps) :
    ProofModeM Expr := do
  let goal' := stripFv goal
  if goal' == goal then return ← k goal
  let h ← k goal'
  let heq ← mkExpectedTypeHint (← mkEqRefl goal) (← mkEq goal goal')
  mkAppNamed ``tac_goal_defeq [("Δ", ehyps), ("P", goal), ("Q", goal'), ("!h", h), ("!heq", heq)]

/-- Evaluate the `subst'`/`subst` applications at the head of `e`, with a proof
(`none`: unchanged). `vals` collects the substituted values; `dirty` is set if
some `subst` could not be evaluated. -/
partial def evalSubstsPf (ext : Expr) (vals : IO.Ref (Array Expr)) (dirty : IO.Ref Bool)
    (e : Expr) : MetaM (Expr × Option Expr) := do
  let e ← instantiateMVars e
  let orRefl (e : Expr) (p? : Option Expr) : MetaM Expr := match p? with
    | some p => pure p
    | none => mkEqRefl e
  if e.isAppOfArity ``Perennial.subst' 4 then
    let b := e.getArg! 1
    let v := e.getArg! 2
    let body := e.getArg! 3
    let (body', pb?) ← evalSubstsPf ext vals dirty body
    match ← binderLit? b with
    | some none =>
      return (body', some (mkAppN (mkConst ``subst'_pf_anon) #[ext, v, body, body', ← orRefl body pb?]))
    | some (some x) =>
      let xe := (← whnfR b).getArg! 0
      vals.modify (·.push v)
      let (r, pr) ← substPf ext x xe v dirty body'
      return (r, some (mkAppN (mkConst ``subst'_pf_named) #[ext, xe, v, body, body', r, ← orRefl body pb?, pr]))
    | none =>
      dirty.set true
      match pb? with
      | none => return (e, none)
      | some pb =>
        let f := mkApp3 (mkConst ``Perennial.subst') ext b v
        return (mkApp f body', some (← mkCongrArg f pb))
  if e.isAppOfArity ``Perennial.subst 4 then
    let xe := e.getArg! 1
    let v := e.getArg! 2
    let body := e.getArg! 3
    let (body', pb?) ← evalSubstsPf ext vals dirty body
    match ← strLit? xe with
    | some x =>
      vals.modify (·.push v)
      let (r, pr) ← substPf ext x xe v dirty body'
      return (r, some (mkAppN (mkConst ``subst_pf_cong) #[ext, xe, v, body, body', r, ← orRefl body pb?, pr]))
    | none =>
      dirty.set true
      match pb? with
      | none => return (e, none)
      | some pb =>
        let f := mkApp3 (mkConst ``Perennial.subst) ext xe v
        return (mkApp f body', some (← mkCongrArg f pb))
  return (e, none)

/-- Simplify the reduct `e2` of a step and fill the evaluation context `K`
around it: returns `fill K e2'` and a proof of `fill K e2 = fill K e2'` (only
the reduct is simplified; the context is already in normal form).

Substitutions are evaluated by `evalSubstsPf` (with a kernel-cheap proof). The
`goose_wp_simp` simp set is then only run if it could change something: the
expression of a WP goal is kept in `goose_wp_simp` normal form, so after a
substitution only the substituted values need to be checked (`needsGooseSimp`). -/
def simpReduct (ext : Expr) (K : List Expr) (e2 : Expr) : MetaM (Expr × Option Expr) := do
  let vals ← IO.mkRef #[]
  let dirty ← IO.mkRef false
  let (e2s, p1?) ← evalSubstsPf ext vals dirty e2
  let vals ← vals.get
  let needs ← if !vals.isEmpty && !(← dirty.get) then vals.anyM needsGooseSimp
    else needsGooseSimp e2s
  let (e2', p2?) ← if needs then gooseExprSimp e2s else pure (e2s, none)
  let p? ← match p1?, p2? with
    | none, none => pure none
    | some p, none => pure (some p)
    | none, some p => pure (some p)
    | some p1, some p2 => some <$> mkEqTrans p1 p2
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

initialize laterCache : IO.Ref (Std.HashMap Expr Bool) ← IO.mkRef {}

/-- Does some hypothesis mention `▷`? (Cached per hypothesis type.) -/
partial def hypsHaveLater {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) :
    MetaM Bool := do
  match hyps with
  | .emp _ => return false
  | .sep _ _ _ _ lhs rhs => return (← hypsHaveLater rhs) || (← hypsHaveLater lhs)
  | .hyp _ _ _ _ ty _ =>
    let ty ← instantiateMVars ty
    if let some b := (← laterCache.get)[ty]? then return b
    let b := (ty.find? fun s => s.isConstOf ``BIBase.later || s.isConstOf ``BIBase.laterN).isSome
    laterCache.modify fun c => (if c.size > 100000 then {} else c).insert ty b
    return b

/-- Introduce a `▷` in front of the hypotheses: `hyps ⊢ ▷ hyps'`, stripping laters
from the hypotheses (Rocq `MaybeIntoLaterNEnvs`). When no hypothesis mentions `▷`,
this is `laterN_intro` (`hyps' = hyps`), avoiding a typeclass search per
hypothesis on every step. -/
def iLaterIntro {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) : ProofModeM ((e' : Q($prop)) × Hyps bi e' × Expr) := do
  if ← hypsHaveLater hyps then
    let ⟨e', hyps', pf⟩ ← iModAction (prop1 := prop) (bi1 := bi) hyps (← laterModality prop bi)
    return ⟨e', hyps', pf⟩
  let pf ← mkAppOptM ``laterN_intro #[some prop, some bi, some (mkNatLit 1), some ehyps]
  return ⟨ehyps, hyps, pf⟩

/-- Find the pure step that `iWpPureStep` would take (the outermost redex with a
`PureWp` instance satisfying `pred`) and solve its side condition. -/
def iWpPureStepFind (wp : GooseWpGoal) (failOnUnsolved : Bool)
    (pred : Expr → MetaM Bool := fun _ => pure true) (multi : Bool := false) :
    ProofModeM (PureStep × Expr) := do
  let gs ← gooseGSArgs wp.ι
  let stepSliceLits := (goose.wp.unfoldSliceLiterals.get (← getOptions)).or
    (!goose.wp.extras.get (← getOptions))
  let some (st, _, _) ← findEctx wp.e (fun K e1 => do
      unless ← pred e1 do throwError "skip"
      -- a head redex has values in its evaluation positions (all `PureWp`
      -- instances are of this form): skip the (costly) instance search otherwise
      -- (instances may match curried applications `App (App (Val f) (Val v1)) (Val v2)`)
      if let some (_, hole) ← extractEctxItem e1 then
        let rec valApp (fuel : Nat) (h : Expr) : MetaM Bool := do
          if (← isGooseVal? h).isSome then return true
          match fuel with
          | 0 => return false
          | fuel + 1 =>
            let h ← whnfR h
            let_expr Perennial.expr.App _ f a := h | return false
            return (← valApp fuel a) && (← valApp fuel f)
        unless ← valApp 8 hole do throwError "skip"
      let some (φ, e2, inst) ← synthPureWp gs e1 | throwError "no PureWp instance"
      -- `wp_pures`/`wp_auto` stop at slice composite literals (as in Rocq, where
      -- `go.composite_literal_slice` is not an instance): use `wp_slice_literal`
      if multi && !stepSliceLits then
        if (← instantiateMVars inst).getUsedConstants.contains
            `Perennial.go.SliceSemantics.composite_literal_slice then
          throwError "slice literal"
      return ({ K, e1, φ, e2, inst } : PureStep))
    | throwIPMError "could not find a head subexpression with a known next step"
  let hφ ← solvePureSideCondition st.φ failOnUnsolved
  return (st, hφ)

/-- Take the pure step `st` found by `iWpPureStepFind`. -/
def iWpPureStepTake {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (st : PureStep) (hφ : Expr) (lc : Bool) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let ⟨ehyps', hyps', hlater⟩ ← iLaterIntro hyps
  let (e', heq?) ← simpReduct wp.ext st.K (← instantiateMVars st.e2)
  let heq ← wp.wrapEq e' heq?
  let Kq := wp.quoteK st.K
  let k := fun (h : Expr) => mkAppNamed (if lc then ``tac_wp_pure_wp_lc' else ``tac_wp_pure_wp')
    [("Hwp", st.inst), ("K", Kq), ("e1", st.e1), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ),
     ("hφ", hφ), ("hlater", hlater), ("e'", wp.wrap e'), ("!heq", heq),
     (if lc then "h" else "!h", h)]
  return ⟨ehyps', hyps', e', k⟩

/-- Take one pure step in the WP goal `hyps ⊢ wp`. Returns the new context,
the new (simplified) expression, and a function turning a proof of the new goal
(`hyps' ⊢ WP e' ...`, or `hyps' ⊢ £ 1 -∗ WP e' ...` when `lc`) into a proof of
the old one. `pred` restricts the redexes considered. -/
def iWpPureStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (failOnUnsolved lc : Bool)
    (pred : Expr → MetaM Bool := fun _ => pure true) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let (st, hφ) ← iWpPureStepFind wp failOnUnsolved pred
  iWpPureStepTake hyps wp st hφ lc

/-- Simplify the expression of the WP goal with `goose_wp_simp`. Returns the new
(inner) expression and a function turning a proof of the new goal into a proof
of the old one, or `none` if nothing changed. -/
def iWpExprSimp (wp : GooseWpGoal) (Δ : Expr) : MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  unless ← needsGooseSimp wp.e do return none
  let (e', p?) ← gooseExprSimp wp.e
  let some _ := p? | return none
  if e' == wp.e then return none
  let heq ← wp.wrapEq e' p?
  return some (e', fun h => mkAppNamed ``tac_wp_expr_simp
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e), ("e'", wp.wrap e'),
     ("!h", h), ("!heq", heq)])

/-- A value constant in evaluation position: a subterm `Val c` (an immediate
argument of a subexpression in evaluation position) where `c` is an application
of a (non-irreducible, non-projection) definition whose unfolding is a value that
is not a function (`#x` or a `val` constructor other than `RecV`), e.g. a Go
package constant `def a : val := #(W64 3)`. Returns `(c, unfolding)`. -/
def findValConst (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  -- a value constant `c`, or one inside `PairV`/`InjLV`/`InjRV`
  let rec check : Nat → Expr → MetaM (Option (Expr × Expr))
  | 0, _ => return none
  | fuel + 1, c => do
    let c ← whnfR c
    let .const n _ := c.getAppFn | return none
    if [``Perennial.val.PairV, ``Perennial.val.InjLV, ``Perennial.val.InjRV].contains n then
      for a in c.getAppArgs.extract 1 c.getAppNumArgs do
        if let some r ← check fuel a then return some r
      return none
    if env.isProjectionFn n || (env.find? n).any (·.isCtor) then return none
    if (← getReducibilityStatus n) == .irreducible then return none
    let some c' ← unfoldDefinition? c | return none
    let c'' ← whnfR c'
    let ok := c''.isAppOf ``GoGlobalContext.into_val ||
      (match c''.getAppFn with
       | .const m _ => m != ``Perennial.val.RecV && (env.find? m).any (·.isCtor)
       | _ => false)
    return if ok then some (c, c') else none
  for (_, e') in ← allEctx e do
    let e' ← whnfR (← instantiateMVars e')
    for a in e'.getAppArgs do
      let a ← whnfR a
      let_expr Perennial.expr.Val _ c := a | continue
      if let some r ← check 8 c then return some r
  return none

/-- Unfold one value constant in evaluation position (`findValConst`) in the WP
goal (definitional). Used by `wp_auto` when no other step applies. -/
def iWpUnfoldValConst? (wp : GooseWpGoal) (Δ : Expr) :
    MetaM (Option (Expr × (Expr → MetaM Expr))) := do
  let some (c, c') ← findValConst wp.e | return none
  let e' := wp.e.replace fun s => if s == c then some c' else none
  if e' == wp.e then return none
  let heq ← mkExpectedTypeHint (← mkEqRefl (wp.wrap wp.e)) (← mkEq (wp.wrap wp.e) (wp.wrap e'))
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
  -- only the search is allowed to fail; errors while taking the step (e.g. in
  -- `simp`) are reported
  let found ← observing? (iWpPureStepFind wp (failOnUnsolved := true) (multi := true))
  let step ← match found with
    | some (st, hφ) => some <$> iWpPureStepTake hyps wp st hφ false
    | none => pure none
  match step with
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

/-- Does the GooseLang expression `e` match the pattern `p` (reducible
`isDefEq`)? Head symbols are compared first, so that most candidates are rejected
without unification, and errors (including running out of heartbeats) count as
no match. -/
def gooseMatchesPattern (e p : Expr) : MetaM Bool := do
  let e' ← whnfR e
  let p' ← whnfR (← instantiateMVars p)
  if let .const pn _ := p'.getAppFn then
    match e'.getAppFn with
    | .const en _ =>
      unless en == pn && e'.getAppNumArgs == p'.getAppNumArgs do return false
    | .mvar .. => pure ()
    | _ => return false
  tryCatchRuntimeEx (withReducible (isDefEq e p)) (fun _ => return false)

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
        Pure.pure (fun e => withNewMCtxDepth (gooseMatchesPattern e p) : Expr → MetaM Bool)
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
            unless ← gooseMatchesPattern e p do throwError "no match"
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
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (lc : Bool := false) (onlyImpl : Bool := false) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Expr × (Expr → MetaM Expr)) := do
  let some ((fv, v2, f, x, body), K, _) ← findEctx wp.e (fun _ e => do
      let e ← whnfR e
      let_expr Perennial.expr.App _ e1 e2 := e | throwError "not an application"
      let some fv ← isGooseVal? e1 | throwError "not a value"
      let some v2 ← isGooseVal? e2 | throwError "not a value"
      -- `onlyImpl`: only implementation constants `«Fooⁱᵐᵖˡ»` (as produced by
      -- `wp_func_call`/`wp_method_call`)
      if onlyImpl then
        let some n := (← instantiateMVars fv).getAppFn.constName? | throwError "not a constant"
        unless (n.toString.endsWith "ⁱᵐᵖˡ") || (n.toString.endsWith "ⁱᵐᵖˡ»") do
          throwError "not an implementation constant"
      let fv' ← whnf fv
      let_expr Perennial.val.RecV _ f x body := fv' | throwError "not a function"
      return (fv, v2, f, x, body))
    | throwIPMError "could not find a function call expression at the head"
  let ⟨ehyps', hyps', hlater⟩ ← iLaterIntro hyps
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
  withNoSorry `wp_apply <| ProofModeM.runTactic `wp_apply fun mvar {prop, bi, hyps, goal, ..} => do
    let some wp ← parseGooseWp? goal | throwIPMError "the goal {goal} is not a GooseLang WP"
    let ⟨ehypsP, hypsP, p, A, posePf⟩ ← iHave hyps goal pmt true
    let Δ : Q($prop) := q(iprop($ehypsP ∗ □?$p $A))
    -- try the `wp_bind_next` position first (as Rocq does), then every position,
    -- outermost first
    let next := (← findBindNext wp.e).toList
    for (K, e') in next ++ (← allEctx wp.e) do
      if let some pf ← observing? (iWpBindCore Δ wp K e' (fun goal' => iApply hypsP p A goal')) then
        mvar.assign (mkApp posePf pf).headBeta
        -- tag the continuation (the last goal whose conclusion mentions the
        -- postcondition `Φ`), for `wp_apply`'s `as` and automation
        for g in (← getThe ProofModeM.State).goals.reverse do
          if let some ig := parseIrisGoal? (← instantiateMVars (← g.getType)) then
            if (ig.goal.find? (· == wp.Φ)).isSome then
              g.setTag `wp_apply_cont
              break
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
    let tag ← mv.getTag
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
    -- keep the `wp_apply_cont` tag of the continuation
    if tag == `wp_apply_cont then
      if let [g'] ← getGoals then g'.setTag tag
    out := out ++ (← getGoals)
  setGoals out

open Lean Elab Tactic in
/-- Internal: remove the `wp_apply_cont` tag set by `wp_apply_raw`. -/
elab "wp_untag_cont" : tactic => do
  for g in ← getUnsolvedGoals do
    if (← g.getTag) == `wp_apply_cont then g.setTag .anonymous

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
  `(tactic| focus ((wp_apply_raw $pmt) <;> wp_apply_post); wp_untag_cont)

end Perennial
