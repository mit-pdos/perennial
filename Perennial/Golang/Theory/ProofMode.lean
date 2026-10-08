/-
The `PureWp` class and the core WP
tactics for GooseLang (`wp_pure`, `wp_pures`, `wp_pure_lc`, `wp_call`,
`wp_bind`, `wp_apply_core`, `wp_value`, `wp_finish`, `wp_expr_simp`).

The tactics are Lean elaborators over the iris-lean proof mode, modeled after
iris-lean's `Iris/HeapLang/ProofMode.lean`.

## Design notes

* `PureWp φ e e'` has `φ` and `e'` as `outParam`s, so ordinary typeclass
  search finds the next step of `e`.
* `wp_call` (which should only fire on a syntactic `RecV`) is an
  ordinary instance: Lean's discrimination trees never unfold the head
  `Val (RecV ...)`, so a sealed definition hidden behind a constant is not
  called accidentally. The `wp_call` tactic additionally unfolds a constant head.
* After each step, the expression is simplified with the `goose_wp_simp` simp
  set: substitution (`subst`, `subst'`) is computed, `fill` is unfolded.
* WP goals are any iris-lean `Wp.wp` over GooseLang's `expr` (the `IrisGS_gen`
  instance is `goose_irisGS`, built from `gooseGlobalGS`/`gooseLocalGS`, or from
  `heapGS`), with stuckness `s`.
-/
import Perennial.GooseLang.Lifting
import Perennial.GooseLang.Countable
import Perennial.Golang.Theory.SimpAttr
import Perennial.Golang.Theory.SubstSimp
import Perennial.Golang.Theory.SubstEnv
import Perennial.Golang.Theory.TacticsSimpAttr
import Perennial.Golang.Theory.IrisTactics
import Perennial.GooseLang.Notation
import Iris.ProofMode

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## The `PureWp` class -/

section classes
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- Classes that are used to tell `wp_pures` about steps it can take:
`PureWp φ e e'` says that, under the pure side condition `φ`, `e` takes a
step (yielding a later credit) to `e'`, in any evaluation context. -/
class PureWp (φ : outParam Prop) (e : Expr) (e' : outParam Expr) : Prop where
  pure_wp_wp : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF) (K : List EctxItem), φ →
    iprop(▷ (£ 1 -∗ WP (fill K e') @ s; E {{ Φ }})) ⊢ WP (fill K e) @ s; E {{ Φ }}

export PureWp (pure_wp_wp)

theorem tac_wp_pure_wp {φ : Prop} {e1 e2 : Expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (h : Δ' ⊢ WP (fill K e2) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  hlater.trans <| (later_mono (wand_intro (sep_elim_left.trans h))).trans
    (Hwp.pure_wp_wp s E Φ K hφ)

theorem tac_wp_pure_wp_later_credit {φ : Prop} {e1 e2 : Expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (h : Δ' ⊢ iprop(£ 1 -∗ WP (fill K e2) @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  hlater.trans <| (later_mono h).trans (Hwp.pure_wp_wp s E Φ K hφ)

/-- `tac_wp_pure_wp` with the reduct given up to an equation (used by the
tactics, which simplify the reduct). -/
theorem tac_wp_pure_wp' {φ : Prop} {e1 e2 e' : Expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (heq : fill K e2 = e') (h : Δ' ⊢ WP e' @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  tac_wp_pure_wp (Hwp := Hwp) hφ hlater (heq ▸ h)

theorem tac_wp_pure_wp_lc' {φ : Prop} {e1 e2 e' : Expr} [Hwp : PureWp (G := G) (L := L) φ e1 e2]
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hφ : φ) (hlater : Δ ⊢ ▷ Δ') (heq : fill K e2 = e')
    (h : Δ' ⊢ iprop(£ 1 -∗ WP e' @ s; E {{ Φ }})) :
    Δ ⊢ WP (fill K e1) @ s; E {{ Φ }} :=
  tac_wp_pure_wp_later_credit (Hwp := Hwp) hφ hlater (heq ▸ h)

/-- Establish `PureWp` from a one-step `PureExec`. -/
theorem pure_exec_pure_wp {φ : Prop} {e e' : Expr} (H : Language.PureExec φ 1 e e') :
    PureWp (G := G) (L := L) φ e e' where
  pure_wp_wp s E Φ K hφ := by
    have := Language.pureExec_fill (fill K) H
    exact wp_pure_step_later (φ := φ) (n := 1) hφ

/-- Establish `PureWp` for an expression `e` that reduces (in any number of
steps) to the value `v'`, given a WP for `e` itself. -/
theorem pure_wp_val (φ : Prop) (e : Expr) (v' : val)
    (Hwp : ∀ (s : Stuckness) (E : CoPset) (Φ : val → IProp GF), φ → iprop(▷ (£ 1 -∗ Φ v')) ⊢ WP e @ s; E {{ Φ }}) :
    PureWp (G := G) (L := L) φ e (Val v') where
  pure_wp_wp s E Φ K hφ := by
    refine .trans ?_ (wp_bind (fill K))
    exact Hwp s E (fun v => WP (fill K (Val v)) @ s; E {{ Φ }}) hφ

end classes

/-! ## Basic instances -/

section instances
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

instance wp_snd (v1 v2 : val) : PureWp (G := G) (L := L) True (Snd (Val (PairV v1 v2))) (Val v2) :=
  pure_exec_pure_wp (pure_snd v1 v2)

instance wp_fst (v1 v2 : val) : PureWp (G := G) (L := L) True (Fst (Val (PairV v1 v2))) (Val v1) :=
  pure_exec_pure_wp (pure_fst v1 v2)

instance wp_recc (f x : Binder) (erec : Expr) :
    PureWp (G := G) (L := L) True (Rec f x erec) (Val (RecV f x erec)) :=
  pure_exec_pure_wp (pure_recc f x erec)

instance wp_pair (v1 v2 : val) :
    PureWp (G := G) (L := L) True (Pair (Val v1) (Val v2)) (Val (PairV v1 v2)) :=
  pure_exec_pure_wp (pure_pairc v1 v2)

instance wp_if_false (e1 e2 : Expr) : PureWp (G := G) (L := L) True (If (Val #false) e1 e2) e2 :=
  pure_exec_pure_wp (pure_if_false e1 e2)

instance wp_if_true (e1 e2 : Expr) : PureWp (G := G) (L := L) True (If (Val #true) e1 e2) e1 :=
  pure_exec_pure_wp (pure_if_true e1 e2)

/-- Calling a function value (see the module docstring). -/
instance wp_call (v2 : val) (f x : Binder) (e : Expr) :
    PureWp (G := G) (L := L) True (App (Val (RecV f x e)) (Val v2))
      (subst' x v2 (subst' f (RecV f x e) e)) :=
  pure_exec_pure_wp (pure_beta f x e v2)

instance pure_wp_LiteralValue (l : List keyed_element) :
    PureWp (G := G) (L := L) True (LiteralValue l) (Val (LiteralValueV l)) :=
  pure_exec_pure_wp (pure_literal_value l)

instance pure_wp_SelectStmtClauses (d : Option Expr) (cs : List comm_clause) :
    PureWp (G := G) (L := L) True (SelectStmtClauses d cs) (Val (SelectStmtClausesV d cs)) :=
  pure_exec_pure_wp (pure_select_stmt_clauses d cs)

-- `wp_call_go_func` (which needs `go.PreSemantics`, `Golang/Defn/Pre.lean`) is at the start of
-- `PostLifting.lean`, so that this file does not wait for `Golang/Defn`.

end instances

/-! ## Runs of `let:`s of values

`wp_auto`/`wp_pures` step through a run `let: x₀ := #v₀ in let: x₁ := #v₁ in ... e`
with an environment `σ` (`SubstEnv.lean`): the goal `WP (fill K (substEnv σ e))`
with `e` a subterm of the original expression is stepped (two pure steps per
`let:`) by extending `σ`, in constant size per `let:`, and only the body after the
run is substituted, once. (Substituting each `let:` into the rest of the run
instead costs the size of the rest of the run per `let:`.) -/

section let_env
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem tac_wp_let_env {σ : String → Option val} {b : Binder} {v : val} {e : Expr}
    {K : List EctxItem} {Δ Δ1 Δ2 : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (h1 : Δ ⊢ ▷ Δ1) (h2 : Δ1 ⊢ ▷ Δ2)
    (h : Δ2 ⊢ WP (fill K (substEnv (envInsB b v σ) e)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (substEnv σ (App (Rec BAnon b e) (Val v)))) @ s; E {{ Φ }} := by
  have he : substEnv σ (App (Rec BAnon b e) (Val v)) =
      App (Rec BAnon b (substEnv (envDel BAnon (envDel b σ)) e)) (Val v) := by
    simp only [substEnv]
  rw [he]
  refine tac_wp_pure_wp (K := EctxItem.AppLCtx v :: K) (Hwp := wp_recc _ _ _) trivial h1 ?_
  refine tac_wp_pure_wp (K := K) (Hwp := wp_call _ _ _ _) trivial h2 ?_
  rw [subst'_substEnv]
  exact h

theorem tac_wp_env_enter {e : Expr} {K : List EctxItem} {Δ : IProp GF} {s : Stuckness}
    {E : CoPset} {Φ : val → IProp GF}
    (h : Δ ⊢ WP (fill K (substEnv envNil e)) @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K e) @ s; E {{ Φ }} := by
  rwa [substEnv_nil] at h

end let_env

/-! ## Lemmas used by the tactics -/

section lemmas
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [ι : IrisGS_gen hlc Expr GF]

theorem tac_wp_bind {Δ : IProp GF} {s : Stuckness} {E : CoPset} {K : List EctxItem} {e' : Expr}
    {Φ : val → IProp GF}
    (H : Δ ⊢ WP e' @ s; E {{ v, WP (fill K (Val v)) @ s; E {{ Φ }} }}) :
    Δ ⊢ WP (fill K e') @ s; E {{ Φ }} :=
  H.trans (wp_bind (fill K))

/-- The postcondition of `e` in `WP (fill K e) {{ Φ }}` (`wp_nestedPost`): the
evaluation context `K` is moved into the postcondition, one `WP` per item. Used
by `wp_auto`/`wp_pures` to work on a redex deep inside an evaluation context
(e.g. in the field-by-field load of a wide struct) in constant time per step. -/
def wpNestedPost (s : Stuckness) (E : CoPset) (K : List EctxItem) (Φ : val → IProp GF) :
    val → IProp GF :=
  match K with
  | [] => Φ
  | Ki :: K' => fun v => WP (fillItem Ki (Val v)) @ s; E {{ wpNestedPost s E K' Φ }}

theorem wp_nestedPost {s : Stuckness} {E : CoPset} {K : List EctxItem} {e : Expr}
    {Φ : val → IProp GF} :
    WP (fill K e) @ s; E {{ Φ }} ⊣⊢ WP e @ s; E {{ wpNestedPost s E K Φ }} := by
  induction K generalizing e with
  | nil => exact .rfl
  | cons Ki K ih =>
    refine (ih (e := fillItem Ki e)).trans ⟨?_, ?_⟩
    · exact wp_bind_inv (fill [Ki]) (e := e)
    · exact wp_bind (fill [Ki]) (e := e)

theorem tac_wp_focus {Δ : IProp GF} {s : Stuckness} {E : CoPset} {K : List EctxItem} {e : Expr}
    {Φ : val → IProp GF} (h : Δ ⊢ WP e @ s; E {{ wpNestedPost s E K Φ }}) :
    Δ ⊢ WP (fill K e) @ s; E {{ Φ }} := h.trans wp_nestedPost.2

theorem tac_wp_unfocus {Δ : IProp GF} {s : Stuckness} {E : CoPset} {K : List EctxItem} {e : Expr}
    {Φ : val → IProp GF} (h : Δ ⊢ WP (fill K e) @ s; E {{ Φ }}) :
    Δ ⊢ WP e @ s; E {{ wpNestedPost s E K Φ }} := h.trans wp_nestedPost.1

theorem tac_wp_value {Δ : IProp GF} {s : Stuckness} {E : CoPset} {v : val} {Φ : val → IProp GF}
    (H : Δ ⊢ |={E}=> Φ v) : Δ ⊢ WP (Val v) @ s; E {{ Φ }} :=
  H.trans (wp_value_fupd (e := Val v) ⟨rfl⟩).2

theorem tac_wp_value_nofupd {Δ : IProp GF} {s : Stuckness} {E : CoPset} {v : val}
    {Φ : val → IProp GF} (H : Δ ⊢ Φ v) : Δ ⊢ WP (Val v) @ s; E {{ Φ }} :=
  H.trans <| fupd_intro.trans (wp_value_fupd (e := Val v) ⟨rfl⟩).2

theorem tac_wp_expr_simp {Δ : IProp GF} {s : Stuckness} {E : CoPset} {e e' : Expr}
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
variable [ext : FfiSyntax]

@[goose_wp_simp] theorem subst'_BAnon (v : val) (e : Expr) : subst' BAnon v e = e := rfl
@[goose_wp_simp] theorem subst'_BNamed (x : String) (v : val) (e : Expr) :
    subst' (BNamed x) v e = subst x v e := rfl

-- The equations of `subst` are in `goose_wp_simp` too (`SubstSimp.lean`).

end simp_lemmas

theorem decide_inst_eq (p : Prop) (h1 h2 : Decidable p) : @decide p h1 = @decide p h2 := by
  cases h1 <;> cases h2 <;> first | rfl | contradiction

simproc [goose_wp_simp] gooseReduceStrEq (( _ : String) = _) := String.reduceEq
simproc [goose_wp_simp] gooseReduceCtorEq (_ = _) := reduceCtorEq
open Lean Meta in
/-- Evaluate a closed `decide p` (e.g. comparisons of Go string literals in
`exceptionSeq`), by reduction. -/
simproc [goose_wp_simp] gooseReduceDecide (decide _) := fun e => do
  let_expr Decidable.decide p inst := e | return .continue
  if p.hasMVar then return .continue
  -- free variables are only allowed if they are instances (e.g. the section
  -- variable `[FfiSyntax]` in a word literal), which evaluation does not need
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

attribute [goose_wp_simp] ne_eq not_false_eq_true not_true_eq_false Binder.BNamed.injEq
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
variable [ext : FfiSyntax] {x : String} {v : val}

theorem binder_named_ne_named {y : String} (h : x ≠ y) : BNamed x ≠ BNamed y :=
  fun h' => h (Binder.BNamed.inj h')
theorem binder_named_ne_anon : BNamed x ≠ BAnon := nofun

theorem subst_pf_val (w : val) : subst x v (Val w) = Val w := rfl
theorem subst_pf_var_eq : subst x v (Var x) = Val v := by simp [subst]
theorem subst_pf_var_ne {y : String} (h : x ≠ y) : subst x v (Var y) = Var y := by simp [subst, h]
theorem subst_pf_rec {f y : Binder} {e e' : Expr} (hf : BNamed x ≠ f) (hy : BNamed x ≠ y)
    (he : subst x v e = e') : subst x v (Rec f y e) = Rec f y e' := by
  simp only [subst]; rw [if_pos ⟨hf, hy⟩, he]
theorem subst_pf_rec_f {y : Binder} {e : Expr} : subst x v (Rec (BNamed x) y e) = Rec (BNamed x) y e := by
  simp [subst]
theorem subst_pf_rec_y {f : Binder} {e : Expr} : subst x v (Rec f (BNamed x) e) = Rec f (BNamed x) e := by
  simp [subst]
theorem subst_pf_app {a b a' b' : Expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (App a b) = App a' b' := by simp only [subst, ha, hb]
theorem subst_pf_if {a b c a' b' c' : Expr} (ha : subst x v a = a') (hb : subst x v b = b')
    (hc : subst x v c = c') : subst x v (If a b c) = If a' b' c' := by simp only [subst, ha, hb, hc]
theorem subst_pf_pair {a b a' b' : Expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (Pair a b) = Pair a' b' := by simp only [subst, ha, hb]
theorem subst_pf_fst {a a' : Expr} (ha : subst x v a = a') : subst x v (Fst a) = Fst a' := by
  simp only [subst, ha]
theorem subst_pf_snd {a a' : Expr} (ha : subst x v a = a') : subst x v (Snd a) = Snd a' := by
  simp only [subst, ha]
theorem subst_pf_fork {a a' : Expr} (ha : subst x v a = a') : subst x v (Fork a) = Fork a' := by
  simp only [subst, ha]
theorem subst_pf_prim0 (op : PrimOp0) : subst x v (Primitive0 op) = Primitive0 op := rfl
theorem subst_pf_prim1 (op : PrimOp1) {a a' : Expr} (ha : subst x v a = a') :
    subst x v (Primitive1 op a) = Primitive1 op a' := by simp only [subst, ha]
theorem subst_pf_prim2 (op : PrimOp2) {a b a' b' : Expr} (ha : subst x v a = a')
    (hb : subst x v b = b') : subst x v (Primitive2 op a b) = Primitive2 op a' b' := by
  simp only [subst, ha, hb]
theorem subst_pf_extop (op : ffi_opcode) {a a' : Expr} (ha : subst x v a = a') :
    subst x v (ExternalOp op a) = ExternalOp op a' := by simp only [subst, ha]
theorem subst_pf_cmpxchg {a b c a' b' c' : Expr} (ha : subst x v a = a') (hb : subst x v b = b')
    (hc : subst x v c = c') : subst x v (CmpXchg a b c) = CmpXchg a' b' c' := by
  simp only [subst, ha, hb, hc]
theorem subst_pf_newproph : subst x v (NewProph : Expr) = NewProph := rfl
theorem subst_pf_resolve {a b a' b' : Expr} (ha : subst x v a = a') (hb : subst x v b = b') :
    subst x v (ResolveProph a b) = ResolveProph a' b' := by simp only [subst, ha, hb]

-- composite literals (`LiteralValue`): without these the kernel would evaluate
-- `subst` on the element list, deciding the `String` equality of every variable
theorem subst_pf_litval {l l' : List keyed_element} (h : substKeyedElements x v l = l') :
    subst x v (LiteralValue l) = LiteralValue l' := by simp only [subst, h]
theorem subst_pf_kes_nil : substKeyedElements x v [] = [] := by simp only [substKeyedElements]
theorem subst_pf_kes_cons {ke ke' : keyed_element} {l l' : List keyed_element}
    (h1 : substKeyedElement x v ke = ke') (h2 : substKeyedElements x v l = l') :
    substKeyedElements x v (ke :: l) = ke' :: l' := by simp only [substKeyedElements, h1, h2]
theorem subst_pf_ke {k k' : Option key} {el el' : Element} (h1 : substOptKey x v k = k')
    (h2 : substElement x v el = el') :
    substKeyedElement x v (KeyedElement k el) = KeyedElement k' el' := by
  simp only [substKeyedElement, h1, h2]
theorem subst_pf_okey_none : substOptKey x v none = none := by simp only [substOptKey]
theorem subst_pf_okey_field (f : GoString) :
    substOptKey x v (some (KeyField f)) = some (KeyField f) := by simp only [substOptKey]
theorem subst_pf_okey_int (i : Int) :
    substOptKey x v (some (KeyInteger i)) = some (KeyInteger i) := by simp only [substOptKey]
theorem subst_pf_okey_expr (t : go.GoType) {e e' : Expr} (h : subst x v e = e') :
    substOptKey x v (some (KeyExpression t e)) = some (KeyExpression t e') := by
  simp only [substOptKey, h]
theorem subst_pf_okey_lv {l l' : List keyed_element} (h : substKeyedElements x v l = l') :
    substOptKey x v (some (KeyLiteralValue l)) = some (KeyLiteralValue l') := by
  simp only [substOptKey, h]
theorem subst_pf_el_expr (t : go.GoType) {e e' : Expr} (h : subst x v e = e') :
    substElement x v (ElementExpression t e) = ElementExpression t e' := by
  simp only [substElement, h]
theorem subst_pf_el_lv {l l' : List keyed_element} (h : substKeyedElements x v l = l') :
    substElement x v (ElementLiteralValue l) = ElementLiteralValue l' := by
  simp only [substElement, h]

theorem subst'_pf_anon {e e' : Expr} (h : e = e') : subst' BAnon v e = e' := h
theorem subst'_pf_named {e e1 e' : Expr} (h1 : e = e1) (h2 : subst x v e1 = e') :
    subst' (BNamed x) v e = e' := by rw [h1]; exact h2
theorem subst_pf_cong {e e1 e' : Expr} (h1 : e = e1) (h2 : subst x v e1 = e') :
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
@[reducible] def fvClosed [FfiSyntax] (_S : List String) (e : Expr) : Expr := e

section closed
variable [ext : FfiSyntax]

/-- `simp` (e.g. `goose_wp_simp` over the whole WP expression) only rewrites the
annotated term, not the variable set of an annotation. -/
@[congr] theorem fvClosed_congr {S : List String} {e e' : Expr} (h : e = e') :
    fvClosed S e = fvClosed S e' := h ▸ rfl

/-- The environment `σ` binds none of the variables in `S`. -/
def EnvAvoids (S : List String) (σ : String → Option val) : Prop := ∀ s ∈ S, σ s = none

/-- Substituting any environment that binds no variable of `S` does not change `e`
(so in particular substituting a variable not in `S`, `subst_pf_fvClosed`). -/
def ClosedUnder (S : List String) (e : Expr) : Prop := ∀ σ, EnvAvoids S σ → substEnv σ e = e
def ClosedKEs (S : List String) (l : List keyed_element) : Prop :=
  ∀ σ, EnvAvoids S σ → substEnvKes σ l = l
def ClosedKE (S : List String) (ke : keyed_element) : Prop :=
  ∀ σ, EnvAvoids S σ → substEnvKe σ ke = ke
def ClosedOKey (S : List String) (k : Option key) : Prop :=
  ∀ σ, EnvAvoids S σ → substEnvOkey σ k = k
def ClosedElem (S : List String) (el : Element) : Prop :=
  ∀ σ, EnvAvoids S σ → substEnvEl σ el = el

/-- The variable names bound by binders `f`, `y`. -/
def bnames : Binder → List String
  | BAnon => []
  | BNamed s => [s]

variable {S : List String}

theorem closed_val (w : val) : ClosedUnder S (Val w) := fun _ _ => by simp only [substEnv]
theorem closed_var {y : String} (h : y ∈ S) : ClosedUnder S (Var y) := by
  intro σ hσ; simp only [substEnv, hσ y h]
theorem closed_rec {f y : Binder} {e : Expr} (h : ClosedUnder (bnames f ++ bnames y ++ S) e) :
    ClosedUnder S (Rec f y e) := by
  intro σ hσ; simp only [substEnv]
  rw [h]
  intro s hs
  simp only [envDel_apply]
  simp only [List.mem_append] at hs
  rcases hs with (hm | hm) | hm
  · cases f <;> simp [bnames] at hm; subst hm; simp
  · cases y <;> simp [bnames] at hm; subst hm; simp
  · simp [hσ s hm]
theorem closed_app {a b : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (App a b) := by intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ]
theorem closed_if {a b c : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) (hc : ClosedUnder S c) :
    ClosedUnder S (If a b c) := by intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ, hc σ hσ]
theorem closed_pair {a b : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (Pair a b) := by intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ]
theorem closed_fst {a : Expr} (ha : ClosedUnder S a) : ClosedUnder S (Fst a) := by
  intro σ hσ; simp only [substEnv, ha σ hσ]
theorem closed_snd {a : Expr} (ha : ClosedUnder S a) : ClosedUnder S (Snd a) := by
  intro σ hσ; simp only [substEnv, ha σ hσ]
theorem closed_fork {a : Expr} (ha : ClosedUnder S a) : ClosedUnder S (Fork a) := by
  intro σ hσ; simp only [substEnv, ha σ hσ]
theorem closed_prim0 (op : PrimOp0) : ClosedUnder S (Primitive0 op) := fun _ _ => by
  simp only [substEnv]
theorem closed_prim1 (op : PrimOp1) {a : Expr} (ha : ClosedUnder S a) :
    ClosedUnder S (Primitive1 op a) := by intro σ hσ; simp only [substEnv, ha σ hσ]
theorem closed_prim2 (op : PrimOp2) {a b : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (Primitive2 op a b) := by intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ]
theorem closed_extop (op : ffi_opcode) {a : Expr} (ha : ClosedUnder S a) :
    ClosedUnder S (ExternalOp op a) := by intro σ hσ; simp only [substEnv, ha σ hσ]
theorem closed_cmpxchg {a b c : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b)
    (hc : ClosedUnder S c) : ClosedUnder S (CmpXchg a b c) := by
  intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ, hc σ hσ]
theorem closed_newproph : ClosedUnder S (NewProph : Expr) := fun _ _ => by simp only [substEnv]
theorem closed_resolve {a b : Expr} (ha : ClosedUnder S a) (hb : ClosedUnder S b) :
    ClosedUnder S (ResolveProph a b) := by intro σ hσ; simp only [substEnv, ha σ hσ, hb σ hσ]
theorem closed_litval {l : List keyed_element} (h : ClosedKEs S l) : ClosedUnder S (LiteralValue l) := by
  intro σ hσ; simp only [substEnv, h σ hσ]
theorem closed_kes_nil : ClosedKEs S [] := by intro σ _; simp only [substEnvKes]
theorem closed_kes_cons {ke : keyed_element} {l : List keyed_element} (h1 : ClosedKE S ke)
    (h2 : ClosedKEs S l) : ClosedKEs S (ke :: l) := by
  intro σ hσ; simp only [substEnvKes, h1 σ hσ, h2 σ hσ]
theorem closed_ke {k : Option key} {el : Element} (h1 : ClosedOKey S k) (h2 : ClosedElem S el) :
    ClosedKE S (KeyedElement k el) := by
  intro σ hσ; simp only [substEnvKe, h1 σ hσ, h2 σ hσ]
theorem closed_okey_none : ClosedOKey S none := by intro σ _; simp only [substEnvOkey]
theorem closed_okey_field (f : GoString) : ClosedOKey S (some (KeyField f)) := by
  intro σ _; simp only [substEnvOkey]
theorem closed_okey_int (i : Int) : ClosedOKey S (some (KeyInteger i)) := by
  intro σ _; simp only [substEnvOkey]
theorem closed_okey_expr (t : go.GoType) {e : Expr} (h : ClosedUnder S e) :
    ClosedOKey S (some (KeyExpression t e)) := by intro σ hσ; simp only [substEnvOkey, h σ hσ]
theorem closed_okey_lv {l : List keyed_element} (h : ClosedKEs S l) :
    ClosedOKey S (some (KeyLiteralValue l)) := by intro σ hσ; simp only [substEnvOkey, h σ hσ]
theorem closed_el_expr (t : go.GoType) {e : Expr} (h : ClosedUnder S e) :
    ClosedElem S (ElementExpression t e) := by intro σ hσ; simp only [substEnvEl, h σ hσ]
theorem closed_el_lv {l : List keyed_element} (h : ClosedKEs S l) :
    ClosedElem S (ElementLiteralValue l) := by intro σ hσ; simp only [substEnvEl, h σ hσ]
/-- A nested annotation with a smaller set. -/
theorem closed_fv {T : List String} {e : Expr} (h : ClosedUnder T e) (hsub : ∀ s ∈ T, s ∈ S) :
    ClosedUnder S (fvClosed T e) := fun σ hσ => h σ (fun s hs => hσ s (hsub s hs))
theorem subset_nil : ∀ s ∈ ([] : List String), s ∈ S := by simp
theorem subset_cons {a : String} {T : List String} (h1 : a ∈ S) (h2 : ∀ s ∈ T, s ∈ S) :
    ∀ s ∈ a :: T, s ∈ S := by
  intro s hs; simp only [List.mem_cons] at hs; rcases hs with rfl | hs; exact h1; exact h2 s hs
theorem not_mem_nil' {x : String} : x ∉ ([] : List String) := by simp
theorem not_mem_cons' {x a : String} {l : List String} (h1 : x ≠ a) (h2 : x ∉ l) : x ∉ a :: l := by
  simp only [List.mem_cons, not_or]; exact ⟨h1, h2⟩

/-- The substitution of a variable `x ∉ S` into an annotated term. -/
theorem subst_pf_fvClosed {x : String} {v : val} {e : Expr} (h : ClosedUnder S e) (hx : x ∉ S) :
    subst x v (fvClosed S e) = fvClosed S e := by
  rw [fvClosed, subst_eq_substEnv]
  apply h
  intro s hs
  have : x ≠ s := fun h' => hx (h' ▸ hs)
  simp [envIns, envNil, this]

theorem env_avoids_nil {σ : String → Option val} : EnvAvoids [] σ := by simp [EnvAvoids]
theorem env_avoids_cons {σ : String → Option val} {a : String} {l : List String}
    (h1 : σ a = none) (h2 : EnvAvoids l σ) : EnvAvoids (a :: l) σ := by
  intro s hs; simp only [List.mem_cons] at hs; rcases hs with rfl | hs; exact h1; exact h2 s hs

/-- The substitution of an environment avoiding `S` into an annotated term. -/
theorem substEnv_pf_fvClosed {σ : String → Option val} {e : Expr} (h : ClosedUnder S e)
    (hσ : EnvAvoids S σ) : substEnv σ (fvClosed S e) = fvClosed S e := h σ hσ

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
    (use `wp_slice_literal`)"
}

/-! ## Meta-level helpers -/

section tactics
open Lean Elab Tactic Meta Qq Iris.ProofMode

/-- Names of the binders of a (∀-)type, in order. -/
private partial def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- Names of context arguments (`GooseWpGoal.ctxArgs`, `PROP`) that `mkAppNamed`
ignores for constants that do not take them. -/
def ctxArgNames : List String := ["hlc", "GF", "ι", "PROP"]

/-- `mkAppNamed c args` when `args` gives every argument of `c` except
instance-implicit ones (which are synthesized): the application is built
directly, without unification. Only binder types with metavariables (e.g.
universe levels) are unified with the types of the given arguments; the kernel
checks the final proof. `none` if some argument is missing. -/
def mkAppNamedDirect? (c : Name) (args : List (String × Lean.Expr)) (partialApp := false) :
    MetaM (Option Lean.Expr) := do
  let info ← getConstInfo c
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let mut ty ← instantiateTypeLevelParams info.toConstantVal us
  let mut out := #[]
  let args := args.map fun (n, v) => (if n.startsWith "!" then (n.drop 1).toString else n, v)
  repeat
    let .forallE n d b bi := ty | break
    let given := args.lookup n.toString
    -- (`partialApp`: the remaining explicit arguments are left out)
    if given.isNone && partialApp && bi == .default then break
    let v ← match given with
      | some v =>
        if d.hasMVar then
          unless ← isDefEq d (← inferType v) do
            throwError "mkAppNamed: type mismatch for argument {n} of {c}"
        pure v
      | none =>
        unless bi == .instImplicit do return none
        synthInstance (← instantiateMVars d)
    out := out.push v
    -- metavariables of `d` (e.g. the universe level of `PROP`) were assigned:
    -- instantiate them in the rest of the type
    let b ← if d.hasMVar then instantiateMVars b else pure b
    ty := b.instantiate1 v
  let us ← us.mapM instantiateLevelMVars
  if us.any (·.hasMVar) then return none
  return some (mkAppN (mkConst c us) out)

/-- Apply constant `c` to the arguments named in `args` (by binder name); all
other arguments are inferred by unification, and remaining instance-implicit
arguments are synthesized. Types of the given arguments are checked with
`isDefEq`, except when `args` gives all the arguments that are not
instance-implicit: then the application is built directly (`mkAppNamedDirect?`),
which avoids unifying (and traversing) the large types of the arguments, and the
kernel checks it. -/
def mkAppNamed (c : Name) (args : List (String × Lean.Expr)) : MetaM Lean.Expr := do
  if let some r ← mkAppNamedDirect? c args then return r
  let info ← getConstInfo c
  let us ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let ty ← instantiateTypeLevelParams info.toConstantVal us
  let names := binderNames ty
  let (mvs, bis, _) ← forallMetaTelescope ty
  -- arguments whose name starts with `!` are assigned without a type check (the
  -- kernel checks the final proof); they are assigned last
  let (unchecked, checked) := args.partition (·.1.startsWith "!")
  for (n, v) in checked do
    let some i := names.idxOf? (Name.mkSimple n)
      | if ctxArgNames.contains n then continue
        throwError "mkAppNamed: {c} has no argument {n}"
    let mv := mvs[i]!
    let mvTy ← instantiateMVars (← inferType mv)
    let vTy ← inferType v
    unless ← isDefEq mvTy vTy do
      throwError "mkAppNamed: type mismatch for argument {n} of {c}:{indentExpr vTy}\n\
        expected{indentExpr mvTy}"
    -- an argument not yet determined by unification is assigned directly: `isDefEq`
    -- would traverse the (possibly large) value to check the assignment
    if ← mv.mvarId!.isAssigned then
      unless ← isDefEq mv v do
        throwError "mkAppNamed: could not assign argument {n} of {c}"
    else
      mv.mvarId!.assign v
  for i in [:mvs.size] do
    if bis[i]! == .instImplicit then
      let mv := mvs[i]!
      unless ← mv.mvarId!.isAssigned do
        let inst ← synthInstance (← instantiateMVars (← inferType mv))
        unless ← isDefEq mv inst do
          throwError "mkAppNamed: could not assign instance argument {i} of {c}"
  let mut raw : Std.HashMap Nat Lean.Expr := {}
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
  wpHead : Lean.Expr
  /-- The `IrisGS_gen` instance. -/
  ι : Lean.Expr
  /-- The `FfiSyntax` instance of the expression type. -/
  ext : Lean.Expr
  s : Lean.Expr
  E : Lean.Expr
  e : Lean.Expr
  Φ : Lean.Expr
  /-- `fill Kl` (partially applied) and `Kl`, for an opaque outer context `Kl`. -/
  tail : Option (Lean.Expr × Lean.Expr) := none

/-- Wrap an inner expression into the opaque outer context of the goal. -/
def GooseWpGoal.wrap (g : GooseWpGoal) (e : Lean.Expr) : Lean.Expr :=
  match g.tail with
  | none => e
  | some (fillKl, _) => mkApp fillKl e

def GooseWpGoal.mk' (g : GooseWpGoal) (e Φ : Lean.Expr) : Lean.Expr :=
  mkAppN g.wpHead #[g.s, g.E, g.wrap e, Φ]

/-- Parse `goal` as a WP over GooseLang expressions. -/
def parseGooseWp? (goal : Lean.Expr) : MetaM (Option GooseWpGoal) := do
  let goal ← instantiateMVars goal
  let goal := goal.consumeMData
  unless goal.isAppOfArity ``Iris.Wp.wp 9 do return none
  let args := goal.getAppArgs
  let exprTy := args[1]!
  let_expr Perennial.Expr ext := exprTy.consumeMData | return none
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
initialize needsCache : IO.Ref (Std.HashMap Lean.Expr Bool) ← IO.mkRef {}
initialize needsConstCache : IO.Ref (Std.HashMap Name Bool) ← IO.mkRef {}

/-- Results of `synthPureWp`, per thread (declarations are elaborated in parallel)
and cleared by every WP tactic (`withNoSorry`). The keys contain the local
instances, so that a result never mentions free variables of another context. -/
initialize pureWpCache :
    IO.Ref (Std.HashMap UInt64 (Std.HashMap Lean.Expr (Option (Lean.Expr × Lean.Expr × Lean.Expr)))) ← IO.mkRef {}

def pureWpCacheFind? (key : Lean.Expr) : BaseIO (Option (Option (Lean.Expr × Lean.Expr × Lean.Expr))) := do
  let tid ← IO.getTID
  return (← pureWpCache.get)[tid]? >>= (·[key]?)

def pureWpCacheInsert (key : Lean.Expr) (r : Option (Lean.Expr × Lean.Expr × Lean.Expr)) : BaseIO Unit := do
  let tid ← IO.getTID
  pureWpCache.modify fun m =>
    let c := m.getD tid {}
    m.insert tid ((if c.size > 10000 then {} else c).insert key r)

def pureWpCacheClear : BaseIO Unit := do
  let tid ← IO.getTID
  pureWpCache.modify (·.erase tid)

/-- Clear the caches of `needsGooseSimp`. -/
def clearNeedsCaches : BaseIO Unit := do
  needsHeadsCache.set none; needsCache.set {}; needsConstCache.set {}

/-- Run the tactic `k` on the main goal with elaboration errors raised as
exceptions (`Term.withoutErrToSorry`, no error recovery), and fail if the proof
it produces contains a (synthetic) `sorry` that was not already in the goal.
All GooseLang WP tactics run under this guard, so that e.g. an ill-typed lemma
given to `wp_apply` is an error rather than a silently admitted goal. -/
def withNoSorry {α} (tacName : Name) (k : TacticM α) : TacticM α := do
  pureWpCacheClear
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
    -- the goal of the proof mode typically mentions assigned (universe level)
    -- metavariables; instantiated here once, so that the hypotheses and the terms
    -- built by the tactics do not contain them (otherwise every `instantiateMVars`
    -- of the growing context traverses it)
    let g ← match parseIrisGoal? (← instantiateMVars (← mvar.getType)) with
      | some g' => pure g'
      | none => pure g
    let some wp ← parseGooseWp? g.goal
      | throwIPMError "the goal {g.goal} is not a GooseLang WP"
    k mvar g wp

/-- One evaluation-context item of a GooseLang expression: the item (as a
`ectx_item` expression) and the sub-expression in the hole. Mirrors
`fillItem` in `Perennial/GooseLang/Lang.lean`. -/
def extractEctxItem (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let e ← whnfR (← instantiateMVars e)
  let isVal (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let e ← whnfR e
    match_expr e with
    | Perennial.Expr.Val _ v => return some v
    | _ => return none
  let mk (n : Name) (ext : Lean.Expr) (args : Array Lean.Expr) : Lean.Expr :=
    mkAppN (mkConst n) (#[ext] ++ args)
  match_expr e with
  | Perennial.Expr.App ext e1 e2 =>
    if let some v ← isVal e2 then return some (mk ``EctxItem.AppLCtx ext #[v], e1)
    else return some (mk ``EctxItem.AppRCtx ext #[e1], e2)
  | Perennial.Expr.If ext e0 e1 e2 => return some (mk ``EctxItem.IfCtx ext #[e1, e2], e0)
  | Perennial.Expr.Pair ext e1 e2 =>
    if let some v ← isVal e1 then return some (mk ``EctxItem.PairRCtx ext #[v], e2)
    else return some (mk ``EctxItem.PairLCtx ext #[e2], e1)
  | Perennial.Expr.Fst ext e => return some (mk ``EctxItem.FstCtx ext #[], e)
  | Perennial.Expr.Snd ext e => return some (mk ``EctxItem.SndCtx ext #[], e)
  | Perennial.Expr.Primitive1 ext op e => return some (mk ``EctxItem.Primitive1Ctx ext #[op], e)
  | Perennial.Expr.Primitive2 ext op e1 e2 =>
    if let some v ← isVal e1 then return some (mk ``EctxItem.Primitive2RCtx ext #[op, v], e2)
    else return some (mk ``EctxItem.Primitive2LCtx ext #[op, e2], e1)
  | Perennial.Expr.ExternalOp ext op e => return some (mk ``EctxItem.ExternalOpCtx ext #[op], e)
  | Perennial.Expr.CmpXchg ext e0 e1 e2 =>
    match ← isVal e0, ← isVal e1 with
    | some v0, some v1 => return some (mk ``EctxItem.CmpXchgRCtx ext #[v0, v1], e2)
    | some v0, none => return some (mk ``EctxItem.CmpXchgMCtx ext #[v0, e2], e1)
    | none, _ => return some (mk ``EctxItem.CmpXchgLCtx ext #[e1, e2], e0)
  | Perennial.Expr.ResolveProph ext e1 e2 =>
    if let some v ← isVal e2 then return some (mk ``EctxItem.ResolveProphLCtx ext #[v], e1)
    else return some (mk ``EctxItem.ResolveProphRCtx ext #[e1], e2)
  | _ => return none

/-- `fillItem Ki e` at the meta level, producing constructor applications. -/
def fillItemExpr (Ki e : Lean.Expr) : MetaM Lean.Expr := do
  let Ki ← whnfR Ki
  let ext := Ki.getAppArgs[0]!
  let a := Ki.getAppArgs
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let val (v : Lean.Expr) : Lean.Expr := mk ``Perennial.Expr.Val #[v]
  match Ki.getAppFn.constName? with
  | some ``EctxItem.AppLCtx => return mk ``Perennial.Expr.App #[e, val a[1]!]
  | some ``EctxItem.AppRCtx => return mk ``Perennial.Expr.App #[a[1]!, e]
  | some ``EctxItem.IfCtx => return mk ``Perennial.Expr.If #[e, a[1]!, a[2]!]
  | some ``EctxItem.PairLCtx => return mk ``Perennial.Expr.Pair #[e, a[1]!]
  | some ``EctxItem.PairRCtx => return mk ``Perennial.Expr.Pair #[val a[1]!, e]
  | some ``EctxItem.FstCtx => return mk ``Perennial.Expr.Fst #[e]
  | some ``EctxItem.SndCtx => return mk ``Perennial.Expr.Snd #[e]
  | some ``EctxItem.Primitive1Ctx => return mk ``Perennial.Expr.Primitive1 #[a[1]!, e]
  | some ``EctxItem.Primitive2LCtx => return mk ``Perennial.Expr.Primitive2 #[a[1]!, e, a[2]!]
  | some ``EctxItem.Primitive2RCtx => return mk ``Perennial.Expr.Primitive2 #[a[1]!, val a[2]!, e]
  | some ``EctxItem.ExternalOpCtx => return mk ``Perennial.Expr.ExternalOp #[a[1]!, e]
  | some ``EctxItem.CmpXchgLCtx => return mk ``Perennial.Expr.CmpXchg #[e, a[1]!, a[2]!]
  | some ``EctxItem.CmpXchgMCtx => return mk ``Perennial.Expr.CmpXchg #[val a[1]!, e, a[2]!]
  | some ``EctxItem.CmpXchgRCtx => return mk ``Perennial.Expr.CmpXchg #[val a[1]!, val a[2]!, e]
  | some ``EctxItem.ResolveProphLCtx => return mk ``Perennial.Expr.ResolveProph #[e, val a[1]!]
  | some ``EctxItem.ResolveProphRCtx => return mk ``Perennial.Expr.ResolveProph #[a[1]!, e]
  | _ => throwError "fillItemExpr: unknown evaluation context item {Ki}"

/-- `fill K e` at the meta level (`K` innermost item first). -/
def fillExpr (K : List Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr :=
  K.foldlM (fun e Ki => fillItemExpr Ki e) e

/-- Quote a list of `ectx_item`s (innermost first), ending in the opaque tail
`tail` (default `[]`). -/
def quoteEctx (ext : Lean.Expr) (K : List Lean.Expr) (tail : Option Lean.Expr := none) : Lean.Expr :=
  let ty := mkApp (mkConst ``EctxItem) ext
  K.foldr (fun Ki acc => mkApp3 (mkConst ``List.cons [0]) ty Ki acc)
    (tail.getD (mkApp (mkConst ``List.nil [0]) ty))

/-- `quoteEctx` with the goal's opaque tail. -/
def GooseWpGoal.quoteK (g : GooseWpGoal) (K : List Lean.Expr) : Lean.Expr :=
  quoteEctx g.ext K (g.tail.map (·.2))

/-- A proof of `fill K e2 = wrap e'` from a proof `p? : fill_items K e2 = e'`
(`none` for `rfl`). -/
def GooseWpGoal.wrapEq (g : GooseWpGoal) (e' : Lean.Expr) (p? : Option Lean.Expr) : MetaM Lean.Expr := do
  match p?, g.tail with
  | none, _ => mkEqRefl (g.wrap e')
  | some p, none => pure p
  | some p, some (fillKl, _) => mkCongrArg fillKl p

/-- Find the *outermost* evaluation context `K` and sub-expression `e'` with
`fill K e' = e` such that `pred K e'` succeeds. Values are
never visited. -/
partial def findEctx {α} (e : Lean.Expr) (pred : List Lean.Expr → Lean.Expr → ProofModeM α) :
    ProofModeM (Option (α × List Lean.Expr × Lean.Expr)) :=
  go e []
where
  go (e : Lean.Expr) (K : List Lean.Expr) : ProofModeM (Option (α × List Lean.Expr × Lean.Expr)) := do
    let e' ← whnfR (← instantiateMVars e)
    if e'.isAppOf ``Perennial.Expr.Val then return none
    if let some a ← observing? (pred K e) then return some (a, K, e)
    let some (Ki, e'') ← extractEctxItem e | return none
    go e'' (Ki :: K)

/-- All evaluation-context decompositions of `e`, outermost first. -/
partial def allEctx (e : Lean.Expr) : MetaM (List (List Lean.Expr × Lean.Expr)) :=
  go e [] []
where
  go (e : Lean.Expr) (K : List Lean.Expr) (acc : List (List Lean.Expr × Lean.Expr)) :
      MetaM (List (List Lean.Expr × Lean.Expr)) := do
    let e' ← whnfR (← instantiateMVars e)
    if e'.isAppOf ``Perennial.Expr.Val then return acc.reverse
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
def reduceMatchersDefault (e : Lean.Expr) : MetaM Lean.Expr := do
  unless goose.wp.extras.get (← getOptions) do return e
  let env ← getEnv
  unless (e.find? fun s => match s with
      | .const n _ => (isMatcherCore env n).or ((n == ``ZeroVal.zeroValDef).or
          ((env.getProjectionFnInfo? n).any (!·.fromClass)))
      | _ => false).isSome do return e
  Meta.transform e (post := fun s => do
    let .const n _ := s.getAppFn | return .continue
    -- a projection of a definition of a constructor application, e.g.
    -- `(zero_val S.t).f'` or `(interface.mk t v).v`
    if let some info := env.getProjectionFnInfo? n then
      -- `zero_val V` of a base type (`W64 0`, `false`, `slice.nil`, ...); the
      -- zero value of a struct stays folded
      if n == ``ZeroVal.zeroValDef then
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
def gooseExprSimp (e : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
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
  gooseExprSimpCore (e : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
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
would do nothing. The subterms `known` are known to be in normal form (e.g. the
subterms of the WP expression that a step only moves around) and are skipped. -/
def needsGooseSimp (e : Lean.Expr) (known : Array Lean.Expr := #[]) : MetaM Bool := do
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
          let rec body : Lean.Expr → Lean.Expr
            | .lam _ _ b _ => body b
            | b => b
          pure ((body v).getAppFn.constName?.any heads.contains)
        | none => pure false
      else pure false
    needsConstCache.modify (·.insert n b)
    return b
  let localNeeds (s : Lean.Expr) : MetaM Bool := do
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
              let b1 := extras.and ((!info.fromClass).or (n == ``ZeroVal.zeroValDef))
              return b1.or ((env.find? c).any (·.isCtor))
            | _ => return false
          else return false
        | none => return false
      | _ => return false
    | _ => return false
  let rec go (s : Lean.Expr) : MetaM Bool := do
    if known.contains s then return false
    if let some b := (← needsCache.get)[s]? then return b
    let b ← do
      if ← localNeeds s then pure true
      else match s with
        -- (the variable set of a closedness annotation is a list of string literals)
        | .app (.app (.app (.const ``fvClosed _) _) _) b => go b
        | .app f a => do if ← go f then pure true else go a
        | .lam _ t b _ | .forallE _ t b _ => do if ← go t then pure true else go b
        | .mdata _ b => go b
        | _ => pure false
    needsCache.modify (·.insert s b)
    return b
  go e

/-- Instance arguments `ext ffi interp sem gctx hlc GF G L` of a `goose_irisGS`
instance. -/
def gooseGSArgs (ι : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let ι ← instantiateMVars ι
  let ι ← if ι.isAppOf ``goose_irisGS then pure ι else whnfR ι
  unless ι.isAppOfArity ``goose_irisGS 9 do
    throwError "the WP is not over the GooseLang `IrisGS_gen` instance `goose_irisGS`:{indentExpr ι}"
  -- `goose_irisGS` takes `ext ffi interp hlc GF sem gctx G L`; return them in the
  -- order of the section variables of this file: `ext ffi interp sem gctx hlc GF G L`
  let a := ι.getAppArgs
  return #[a[0]!, a[1]!, a[2]!, a[5]!, a[6]!, a[3]!, a[4]!, a[7]!, a[8]!]

/-- The context arguments `hlc`, `GF`, `ι` of the tactic lemmas about the WP of `wp`. -/
def GooseWpGoal.ctxArgs (wp : GooseWpGoal) : MetaM (List (String × Lean.Expr)) := do
  let gs ← gooseGSArgs wp.ι
  return [("hlc", gs[5]!), ("GF", gs[6]!), ("ι", wp.ι)]

/-- `mkAppNamed` with the context arguments of `wp` (`GooseWpGoal.ctxArgs`), so
that the application can be built without unification (`mkAppNamedDirect?`). -/
def GooseWpGoal.mkAppNamed (wp : GooseWpGoal) (c : Name) (args : List (String × Lean.Expr)) :
    MetaM Lean.Expr := do
  Perennial.mkAppNamed c ((← wp.ctxArgs) ++ args)

/-- Is the goal's expression a value `Val v` (with no opaque outer context)? -/
def GooseWpGoal.isVal? (g : GooseWpGoal) : MetaM (Option Lean.Expr) := do
  if g.tail.isSome then return none
  let e ← whnfR (← instantiateMVars g.e)
  match_expr e with
  | Perennial.Expr.Val _ v => return some v
  | _ => return none

/-- Is `e` a GooseLang value `Val v`? -/
def isGooseVal? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let e ← whnfR (← instantiateMVars e)
  match_expr e with
  | Perennial.Expr.Val _ v => return some v
  | _ => return none

/-- A pure step found in a WP goal. -/
structure PureStep where
  K : List Lean.Expr
  e1 : Lean.Expr
  φ : Lean.Expr
  e2 : Lean.Expr
  inst : Lean.Expr

/-- The `PureWp` instance of a step that only rearranges `e1`: `Rec f x e`
(`wp_recc`), a beta-redex `App (Val (RecV f x e)) (Val v)` (`wp_call`) and a pair
of values (`wp_pair`), built
directly instead of by typeclass search: unifying the instance with `e1` assigns
the (possibly large) body `e` to a metavariable, which costs a traversal of `e`
at every step. Returns the same as `synthPureWp`. -/
def directPureWp (gs : Array Lean.Expr) (e1 : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  unless gs.size == 9 do return none
  let ext := gs[0]!
  let e ← whnfR (← instantiateMVars e1)
  let val (v : Lean.Expr) := mkApp2 (mkConst ``Perennial.Expr.Val) ext v
  match_expr e with
  | Perennial.Expr.Rec _ f x body =>
    return some (mkConst ``True, val (mkApp4 (mkConst ``Perennial.val.RecV) ext f x body),
      mkAppN (mkConst ``wp_recc) (gs ++ #[f, x, body]))
  | Perennial.Expr.App _ a b =>
    let some fv ← isGooseVal? a | return none
    let some v2 ← isGooseVal? b | return none
    let fv ← whnfR fv
    let_expr Perennial.val.RecV _ f x body := fv | return none
    let recv := mkApp4 (mkConst ``Perennial.val.RecV) ext f x body
    let s1 := mkApp4 (mkConst ``Perennial.subst') ext f recv body
    return some (mkConst ``True, mkApp4 (mkConst ``Perennial.subst') ext x v2 s1,
      mkAppN (mkConst ``wp_call) (gs ++ #[v2, f, x, body]))
  | Perennial.Expr.Pair _ a b =>
    let some v1 ← isGooseVal? a | return none
    let some v2 ← isGooseVal? b | return none
    return some (mkConst ``True, val (mkApp3 (mkConst ``Perennial.val.PairV) ext v1 v2),
      mkAppN (mkConst ``wp_pair) (gs ++ #[v1, v2]))
  | _ => return none

/-- Apply the constant `c` (without universe parameters) to `gs` (its first
arguments) and then to one argument per remaining binder: instance-implicit ones
are synthesized, the others are `args` in order (each given the binder type).
Built directly, without unification: the kernel checks it. -/
def mkAppPositional? (c : Name) (gs : Array Lean.Expr) (args : Array (Lean.Expr → MetaM Lean.Expr)) :
    MetaM (Option Lean.Expr) := do
  let some info := (← getEnv).find? c | return none
  unless info.levelParams.isEmpty do return none
  let mut ty := info.type
  let mut out := #[]
  let mut j := 0
  repeat
    let .forallE _ d b bi := ty | break
    let v ← if h : out.size < gs.size then pure gs[out.size]
      else if bi == .instImplicit then
        match ← synthInstance? d with
        | some v => pure v
        | none => return none
      else if h : j < args.size then do
        j := j + 1
        args[j - 1] d
      else return none
    out := out.push v
    ty := b.instantiate1 v
  return some (mkAppN (mkConst c) out)

/-- The step of an array literal whose elements are all values of the element
type, `App (Val (GoInstruction (CompositeLiteral (go.ArrayType n t)))) (Val
(LiteralValueV kvs))` with `kvs = [KeyedElement none (ElementExpression t (Val #x)), ...]`
and `n` a literal: one `PureWp` step to the array value (`pure_wp_array_lit` of
`Golang/Theory/ArrayLit.lean`, if it is imported), instead of the `ArraySet` chain of
`go.composite_literal_array`, whose stepping is quadratic in the length.
Returns the same as `synthPureWp`. -/
def arrayLitPureWp? (gs : Array Lean.Expr) (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  unless gs.size == 9 do return none
  let e ← whnfR e
  let_expr Perennial.Expr.App _ f a := e | return none
  let some fv ← isGooseVal? f | return none
  let fv ← whnfR fv
  let_expr Perennial.val.GoInstruction _ i := fv | return none
  let i ← whnfR i
  let_expr Perennial.GoInstruction.CompositeLiteral ty := i | return none
  let ty ← whnfR ty
  let_expr Perennial.go.GoType.ArrayType nE t := ty | return none
  let some lv ← isGooseVal? a | return none
  let lv ← whnfR lv
  let_expr Perennial.val.LiteralValueV _ kvs := lv | return none
  unless (← getEnv).contains `Perennial.pure_wp_array_lit do return none
  let some n ← getIntValue? nE | return none
  -- the elements `#x`, all of the same type `V`
  let mut V? : Option Lean.Expr := none
  let mut xs := #[]
  let mut l ← whnfR kvs
  repeat
    match_expr l with
    | List.cons _ ke rest =>
      let ke ← whnfR ke
      let_expr Perennial.keyed_element.KeyedElement _ k el := ke | return none
      unless (← whnfR k).isAppOfArity ``Option.none 1 do return none
      let el ← whnfR el
      let_expr Perennial.Element.ElementExpression _ t' ee := el | return none
      unless t' == t do return none
      let some v ← isGooseVal? ee | return none
      unless v.isAppOfArity ``GoGlobalContext.intoVal 4 do return none
      let V := v.getArg! 2
      if let some V0 := V? then
        unless V0 == V do return none
      else V? := some V
      xs := xs.push (v.getArg! 3)
      l ← whnfR rest
    | List.nil _ => break
    | _ => return none
  let some V := V? | return none
  if V.hasLooseBVars || xs.any (·.hasLooseBVars) then return none
  let N := n.toNat
  unless xs.size ≤ N && N < 2 ^ 63 do return none
  let some zv ← synthInstance? (mkApp (mkConst ``ZeroVal) V) | return none
  let m := N - xs.size
  let xsE ← mkListLit V xs.toList
  let ofDecide (d : Lean.Expr) : MetaM Lean.Expr := do
    let inst ← synthInstance (mkApp (mkConst ``Decidable) d)
    return mkApp3 (mkConst ``of_decide_eq_true) d inst
      (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true))
  let hlen : Lean.Expr → MetaM Lean.Expr := fun _ => mkEqRefl (mkNatLit N)
  let common : Array (Lean.Expr → MetaM Lean.Expr) := #[fun _ => pure nE, fun _ => pure t, fun _ => pure V,
    fun _ => pure zv, fun _ => pure xsE]
  let rest : Array (Lean.Expr → MetaM Lean.Expr) := #[fun _ => pure kvs, fun _ => mkEqRefl kvs, hlen,
    ofDecide]
  let r? : Option Lean.Expr ← if m == 0 then
      mkAppPositional? `Perennial.pure_wp_array_lit_full gs (common ++ rest)
    else
      mkAppPositional? `Perennial.pure_wp_array_lit gs
        (common.push (fun _ => pure (mkNatLit m)) ++ rest)
  let some inst := r? | return none
  let iTy ← inferType inst
  let args := iTy.getAppArgs
  unless args.size == gs.size + 3 do return none
  return some (args[gs.size]!, args[gs.size + 2]!, inst)

/-- Is `e` an application of a constructor of `go.GoType` (e.g. a struct type with its
field list)? Such subterms are treated as atoms by the keys of `synthPureWp`. -/
def isGoTypeApp (e : Lean.Expr) : Bool :=
  match e.getAppFn with
  | .const n _ => n.getPrefix == ``Perennial.go.GoType
  | _ => false

/-- Is `e` small (at most `n` nodes, counting shared subterms repeatedly, and the
payloads `x` of values `#x` as one node when `modPayloads`)? Takes `O(n)`. -/
def exprSmall (e : Lean.Expr) (n : Nat) (modPayloads := false) : Bool :=
  (go n e).isSome
where
  go : Nat → Lean.Expr → Option Nat
    | 0, _ => none
    | fuel + 1, e@(.app f a) =>
      if modPayloads && (e.isAppOfArity ``GoGlobalContext.intoVal 4 || isGoTypeApp e) then
        go fuel f
      else do let fuel ← go fuel f; go fuel a
    | fuel + 1, .mdata _ b => go fuel b
    | fuel + 1, .lam _ t b _ | fuel + 1, .forallE _ t b _ => do let fuel ← go fuel t; go fuel b
    | fuel + 1, _ => some fuel

/-- Is `V` a type whose Go values are matched generically by the `PureWp`
instances, so that the payload `x` of a value `#x` of type `V` can be abstracted
in the key of a search (`synthPureWp`)? Machine words (`BitVec n`) and the struct
types generated by goose: no instance matches on a particular word or struct.
(Not locations, slices, maps, ...: e.g. the comparison of a map with `#map.nil`
has its own instance.) -/
def genericPayloadType (V : Lean.Expr) : MetaM Bool := do
  let V ← whnfR V
  if V.isAppOfArity ``BitVec 1 then return true
  -- the struct types generated by goose (fields `f'`): Go structs are not compared
  -- with constants (unlike pointers, slices, maps, ... with `nil`)
  let .const n _ := V.getAppFn | return false
  let env ← getEnv
  let some info := getStructureInfo? env n | return false
  return !info.fieldNames.isEmpty && info.fieldNames.all fun f =>
    match f with
    | .str _ s => s.endsWith "'"
    | _ => false

/-- If `e` is `StructFieldRef t f` applied to a value: the instruction `StructFieldRef t f`
and `f` (the instances are generic in the field name `f`, so that it can be
abstracted in the key of the search, see `synthPureWp`). -/
def fieldRefName? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let e ← whnfR e
  let_expr Perennial.Expr.App _ fe _ := e | return none
  let some fv ← isGooseVal? fe | return none
  let fv ← whnfR fv
  let_expr Perennial.val.GoInstruction _ i := fv | return none
  let i' ← whnfR i
  unless i'.isAppOf ``GoInstruction.StructFieldRef && i'.getAppNumArgs ≥ 2 do return none
  return some (i, i'.appArg!)

/-- The values `#x` in `e` (below applications) whose payload `x` has a generic type
(`genericPayloadType`), as `(V, x)`, and for each value `#x` (in the order of
`replaceGenericPayloads`) whether it is one of them. -/
def genericPayloads (e : Lean.Expr) : MetaM (Array (Lean.Expr × Lean.Expr) × Array Bool) := do
  let mut acc : Array (Lean.Expr × Lean.Expr) := #[]
  let mut flags : Array Bool := #[]
  for s in collectIntoVals e #[] do
    let x := s.getArg! 3
    let g ← if x.hasLooseBVars then pure false else genericPayloadType (s.getArg! 2)
    flags := flags.push g
    if g then acc := acc.push (s.getArg! 2, x)
  return (acc, flags)
where
  collectIntoVals (e : Lean.Expr) (acc : Array Lean.Expr) : Array Lean.Expr :=
    if e.isAppOfArity ``GoGlobalContext.intoVal 4 then acc.push e
    else if isGoTypeApp e then acc
    else match e with
      | .app f a => collectIntoVals a (collectIntoVals f acc)
      | .mdata _ b => collectIntoVals b acc
      | _ => acc

/-- Replace the payloads found by `genericPayloads e` (`isGeneric`, in the same
order) by `ys`. -/
def replaceGenericPayloads (e : Lean.Expr) (isGeneric : Array Bool) (ys : Array Lean.Expr) : Lean.Expr :=
  (go e 0 0).1
where
  -- returns the new expression, the index of the next `#x` and of the next `y`
  go (e : Lean.Expr) (i j : Nat) : Lean.Expr × Nat × Nat :=
    if e.isAppOfArity ``GoGlobalContext.intoVal 4 then
      if isGeneric[i]?.getD false then
        (mkApp e.appFn! ys[j]!, i + 1, j + 1)
      else (e, i + 1, j)
    else if isGoTypeApp e then (e, i, j)
    else match e with
      | .app f a =>
        let (f', i, j) := go f i j
        let (a', i, j) := go a i j
        (mkApp f' a', i, j)
      | .mdata d b => let (b', i, j) := go b i j; (.mdata d b', i, j)
      | _ => (e, i, j)

/-- The free variables of `e` that are neither let-bound nor local instances
(sorted by declaration order), or `none` if `e` mentions a let-bound variable. -/
def pureWpKeyVars (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let lctx ← getLCtx
  let insts := (← getLocalInstances).map (·.fvar)
  let mut ds := #[]
  for fv in (collectFVars {} e).fvarIds do
    let some d := lctx.find? fv | return none
    if d.isLet then return none
    unless insts.contains (mkFVar fv) do ds := ds.push d
  return some ((ds.qsort (·.index < ·.index)).map (·.toExpr))

/-- The `PureWp` search for `e1` (no shortcut, no cache). -/
def synthPureWpCore (gs : Array Lean.Expr) (e1 : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  let φ ← mkFreshExprMVar (mkSort .zero)
  let e2 ← mkFreshExprMVar (mkApp (mkConst ``Perennial.Expr) gs[0]!)
  let ty ← mkAppOptM ``PureWp (gs.map some ++ #[some φ, some e1, some e2])
  let some inst ← synthInstance? ty | return none
  let ty ← instantiateMVars ty
  let args := ty.getAppArgs
  return some (args[gs.size]!, args[gs.size + 2]!, ← instantiateMVars inst)

/-- Find a `PureWp` instance for `e1`: the structural steps are built directly
(`directPureWp`); for a small redex, the search is done once per *shape* (within
one tactic call, `pureWpCache`): the redex with its free variables (other than
local instances), the payloads of its machine-word and struct values
(`genericPayloadType`) and the field name of a `StructFieldRef` abstracted, so
that e.g. all the steps `#x +⟨go.uint64⟩ #(W64 1)` of a function, or all the field
references of a struct, share one search; a failed generic search is final. A
redex without such payloads is cached up to its free variables. -/
def synthPureWp (gs : Array Lean.Expr) (e1 : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Lean.Expr)) := do
  if let some r ← directPureWp gs e1 then return some r
  if let some r ← arrayLitPureWp? gs e1 then return some r
  let e1 ← instantiateMVars e1
  -- (only small redexes: the key is built at every step)
  if e1.hasMVar.or !(exprSmall e1 400 (modPayloads := true)) then return ← synthPureWpCore gs e1
  -- (the local instances are part of the key: the results may mention them)
  let insts := (← getLocalInstances).map (·.fvar)
  let mkKey (k : Lean.Expr) : MetaM Lean.Expr := pure (mkAppN k insts)
  let inst3 (r : Option (Lean.Expr × Lean.Expr × Lean.Expr)) (args : Array Lean.Expr) :=
    r.map fun (φ, e2, inst) => (φ.beta args, e2.beta args, inst.beta args)
  let abs3 (params : Array Lean.Expr) :
      Option (Lean.Expr × Lean.Expr × Lean.Expr) → MetaM (Option (Option (Lean.Expr × Lean.Expr × Lean.Expr)))
    | none => pure (some none)
    | some (φ, e2, inst) =>
      if φ.hasMVar.or (e2.hasMVar.or inst.hasMVar) then pure none
      else return some (some (← mkLambdaFVars params φ, ← mkLambdaFVars params e2,
        ← mkLambdaFVars params inst))
  -- the generic search, with the payloads abstracted
  let (payloads, isGeneric) ← genericPayloads e1
  -- (and the field name of a `StructFieldRef`)
  let fieldRef? ← fieldRefName? e1
  let payloads ← match fieldRef? with
    | some (_, f) => pure (payloads.push (← inferType f, f))
    | none => pure payloads
  unless payloads.isEmpty do
    let r? ← withLocalDeclsDND (payloads.map fun (V, _) => (`y, V)) fun ys => do
      let e1' := replaceGenericPayloads e1 isGeneric ys
      let e1' := match fieldRef? with
        | some (i, f) =>
          let i' := i.replace fun s => if s == f then some ys.back! else none
          e1'.replace fun s => if s == i then some i' else none
        | none => e1'
      unless exprSmall e1' 400 do
        return none
      let some xs ← pureWpKeyVars e1' | return none
      let xs := xs.filter (!ys.contains ·)
      let params := ys ++ xs
      let key ← mkKey (← mkLambdaFVars params e1')
      if let some r ← pureWpCacheFind? key then
        return some (r, xs)
      let r ← synthPureWpCore gs e1'
      let some ra ← abs3 params r | return none
      pureWpCacheInsert key ra
      return some (ra, xs)
    -- (a failed generic search is final: the instances do not match on the
    -- payloads that are abstracted, see `genericPayloadType`)
    if let some (r, xs) := r? then
      return inst3 r (payloads.map (·.2) ++ xs)
  -- the concrete search (cached up to free variables)
  unless exprSmall e1 400 do return ← synthPureWpCore gs e1
  let some xs ← pureWpKeyVars e1 | return ← synthPureWpCore gs e1
  let key ← mkKey (← mkLambdaFVars xs e1)
  if let some r ← pureWpCacheFind? key then
    return inst3 r xs
  let r ← synthPureWpCore gs e1
  if let some ra ← abs3 xs r then pureWpCacheInsert key ra
  return r

/-- Discharge the side condition `φ` of a pure step. `True` is solved
immediately; otherwise iris-lean's side-condition solver is tried, and if it
fails the condition becomes a new goal (unless `failOnUnsolved`). -/
def solvePureSideCondition (φ : Lean.Expr) (failOnUnsolved : Bool) : ProofModeM Lean.Expr := do
  let φ ← instantiateMVars φ
  if φ.isConstOf ``True then return mkConst ``True.intro
  iSolveSidecondition φ (failOnUnsolved := failOnUnsolved)

/-- Is `e` a string literal? -/
def strLit? (e : Lean.Expr) : MetaM (Option String) := do
  match (← whnfR e).consumeMData with
  | .lit (.strVal s) => return some s
  | _ => return none

/-- A binder literal: `some none` for `BAnon`, `some (some x)` for `BNamed "x"`. -/
def binderLit? (b : Lean.Expr) : MetaM (Option (Option String)) := do
  let b ← whnfR b
  if b.isAppOf ``Binder.BAnon then return some none
  if b.isAppOfArity ``Binder.BNamed 1 then
    if let some x ← strLit? (b.getArg! 0) then return some (some x)
  return none

/-- `subst x v e` computed at the meta level on GooseLang constructor terms
(definitionally equal to `Perennial.subst x v e`; non-constructor subterms are
left as `subst x v _`). -/
partial def substMeta (ext : Lean.Expr) (x : String) (xe v : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  let e ← whnfR e
  let fallback := mkApp4 (mkConst ``Perennial.subst) ext xe v e
  let rec' := substMeta ext x xe v
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Perennial.Expr.Val, _ => return e
  | some ``Perennial.Expr.Var, #[_, y] =>
    match ← strLit? y with
    | some y' => return (if y' == x then mk ``Perennial.Expr.Val #[v] else e)
    | none => return fallback
  | some ``Perennial.Expr.Rec, #[_, f, y, body] =>
    match ← binderLit? f, ← binderLit? y with
    | some fb, some yb =>
      if fb == some x ∨ yb == some x then return mk ``Perennial.Expr.Rec #[f, y, body]
      else return mk ``Perennial.Expr.Rec #[f, y, ← rec' body]
    | _, _ => return fallback
  | some ``Perennial.Expr.App, #[_, a, b] => return mk ``Perennial.Expr.App #[← rec' a, ← rec' b]
  | some ``Perennial.Expr.If, #[_, a, b, c] =>
    return mk ``Perennial.Expr.If #[← rec' a, ← rec' b, ← rec' c]
  | some ``Perennial.Expr.Pair, #[_, a, b] => return mk ``Perennial.Expr.Pair #[← rec' a, ← rec' b]
  | some ``Perennial.Expr.Fst, #[_, a] => return mk ``Perennial.Expr.Fst #[← rec' a]
  | some ``Perennial.Expr.Snd, #[_, a] => return mk ``Perennial.Expr.Snd #[← rec' a]
  | some ``Perennial.Expr.Fork, #[_, a] => return mk ``Perennial.Expr.Fork #[← rec' a]
  | some ``Perennial.Expr.Primitive0, _ => return e
  | some ``Perennial.Expr.Primitive1, #[_, op, a] =>
    return mk ``Perennial.Expr.Primitive1 #[op, ← rec' a]
  | some ``Perennial.Expr.Primitive2, #[_, op, a, b] =>
    return mk ``Perennial.Expr.Primitive2 #[op, ← rec' a, ← rec' b]
  | some ``Perennial.Expr.ExternalOp, #[_, op, a] =>
    return mk ``Perennial.Expr.ExternalOp #[op, ← rec' a]
  | some ``Perennial.Expr.CmpXchg, #[_, a, b, c] =>
    return mk ``Perennial.Expr.CmpXchg #[← rec' a, ← rec' b, ← rec' c]
  | some ``Perennial.Expr.NewProph, _ => return e
  | some ``Perennial.Expr.ResolveProph, #[_, a, b] =>
    return mk ``Perennial.Expr.ResolveProph #[← rec' a, ← rec' b]
  | _, _ => return fallback

/-- Evaluate the `subst'`/`subst` applications at the head of `e` with
`substMeta` (the result is definitionally equal to `e`). -/
partial def evalSubsts (ext : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
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
def strNeProof (a b : String) (ae be : Lean.Expr) : Lean.Expr :=
  let rec go (cs ds : List Char) : Lean.Expr × Lean.Expr × Lean.Expr :=
    -- returns (cs expr, ds expr, proof cs ≠ ds)
    let charE (c : Char) := mkApp (mkConst ``Char.ofNat) (mkRawNatLit c.toNat)
    let nil := mkApp (mkConst ``List.nil [0]) (mkConst ``Char)
    let cons (c t : Lean.Expr) := mkApp3 (mkConst ``List.cons [0]) (mkConst ``Char) c t
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
def binderNeProof (ext : Lean.Expr) (x : String) (xe : Lean.Expr) (b : Option String) (be : Lean.Expr) : Lean.Expr :=
  match b with
  | none => mkApp2 (mkConst ``binder_named_ne_anon) ext xe
  | some y =>
    let ye := (be.getArg! 0)
    mkApp4 (mkConst ``binder_named_ne_named) ext xe ye (strNeProof x y xe ye)

/-- Whether `wp_auto` takes `if: #(decide P) then e else AngelicExit #()` steps
(introducing `P` as an inaccessible hypothesis); set by
`solve_into_val_typed_struct` (`Auto.lean`). -/
initialize autoAngelicIf : IO.Ref Bool ← IO.mkRef false

register_option goose.wp.introSimp : Bool := {
  defValue := true
  descr := "simplify the hypotheses introduced by `wp_apply ... as pats` with the WP simp set"
}

register_option goose.wp.fvAnnot : Bool := {
  defValue := true
  descr := "let `wp_auto` annotate continuations with their free variables, so that \
    substitutions into the rest of a long function are proved in constant size"
}

/-! ### Closedness annotations (meta level) -/

/-- Whether `substPf` uses closedness annotations (`fvClosed`), and the caches of
free-variable sets and closedness proofs (set up by `wp_auto`). -/
initialize fvAnnotMode : IO.Ref Bool ← IO.mkRef false
initialize fvCache : IO.Ref (Std.HashMap Lean.Expr (Option (List String))) ← IO.mkRef {}
initialize closedCache : IO.Ref (Std.HashMap (Lean.Expr × Lean.Expr) (Option Lean.Expr)) ← IO.mkRef {}
/-- Terms that `assignHoisted` may hoist out of binders (`hoistClosed`): the closedness
annotations `fvClosed S e` and their proofs, which are shared by the steps below
binders. In creation order: a term comes after the ones it contains. -/
initialize hoistCandidates : IO.Ref (Array Lean.Expr) ← IO.mkRef #[]

/-- A literal `List String` expression. -/
def strListExpr (l : List String) : Lean.Expr :=
  let ty := mkConst ``String
  l.foldr (fun s acc => mkApp3 (mkConst ``List.cons [0]) ty (mkStrLit s) acc)
    (mkApp (mkConst ``List.nil [0]) ty)

/-- Parse a literal `List String` expression. -/
partial def strList? (e : Lean.Expr) : MetaM (Option (List String)) := do
  let e ← whnfR e
  if e.isAppOfArity ``List.nil 1 then return some []
  unless e.isAppOfArity ``List.cons 3 do return none
  let some s ← strLit? (e.getArg! 1) | return none
  let some t ← strList? (e.getArg! 2) | return none
  return some (s :: t)

/-- A proof of `s ∈ l` for a literal list `l` (as `le`) containing `s`. -/
def memPf (s : String) (l : List String) (le : Lean.Expr) : MetaM (Option Lean.Expr) := do
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
def notMemPf (ext : Lean.Expr) (x : String) (xe : Lean.Expr) (l : List String) : Lean.Expr :=
  match l with
  | [] => mkApp2 (mkConst ``not_mem_nil') ext xe
  | a :: t =>
    let ae := mkStrLit a
    mkApp6 (mkConst ``not_mem_cons') ext xe ae (strListExpr t) (strNeProof x a xe ae)
      (notMemPf ext x xe t)

/-- The free variables of an `expr` built from constructors (`none` if some part
is not), using the annotations `fvClosed S e` (whose set is `S`). -/
partial def fvOf (e : Lean.Expr) : MetaM (Option (List String)) := do
  if let some r := (← fvCache.get)[e]? then return r
  let union (a b : List String) : List String := a ++ b.filter (!a.contains ·)
  let r ← do
    if e.isAppOfArity ``fvClosed 3 then strList? (e.getArg! 1) else
    let e ← whnfR e
    let args := e.getAppArgs
    let all (xs : List Lean.Expr) : MetaM (Option (List String)) := do
      let mut acc := []
      for x in xs do
        let some f ← fvOf x | return none
        acc := union acc f
      return some acc
    match e.getAppFn.constName? with
    | some ``Perennial.Expr.Val => pure (some [])
    | some ``Perennial.Expr.Var => pure ((← strLit? args[1]!).map ([·]))
    | some ``Perennial.Expr.Rec =>
      match ← binderLit? args[1]!, ← binderLit? args[2]!, ← fvOf args[3]! with
      | some f, some y, some b => pure (some (b.filter fun s => some s != f && some s != y))
      | _, _, _ => pure none
    | some ``Perennial.Expr.App => all [args[1]!, args[2]!]
    | some ``Perennial.Expr.If => all [args[1]!, args[2]!, args[3]!]
    | some ``Perennial.Expr.Pair => all [args[1]!, args[2]!]
    | some ``Perennial.Expr.Fst => all [args[1]!]
    | some ``Perennial.Expr.Snd => all [args[1]!]
    | some ``Perennial.Expr.Fork => all [args[1]!]
    | some ``Perennial.Expr.Primitive0 => pure (some [])
    | some ``Perennial.Expr.Primitive1 => all [args[2]!]
    | some ``Perennial.Expr.Primitive2 => all [args[2]!, args[3]!]
    | some ``Perennial.Expr.ExternalOp => all [args[2]!]
    | some ``Perennial.Expr.CmpXchg => all [args[1]!, args[2]!, args[3]!]
    | some ``Perennial.Expr.NewProph => pure (some [])
    | some ``Perennial.Expr.ResolveProph => all [args[1]!, args[2]!]
    -- composite literals (possibly long, e.g. lookup tables) are not annotated
    | some ``Perennial.Expr.LiteralValue => pure none
    | _ => pure none
  fvCache.modify (·.insert e r)
  return r
where
  fvKEs (l : Lean.Expr) : MetaM (Option (List String)) := do
    let l ← whnfR l
    if l.isAppOfArity ``List.nil 1 then return some []
    unless l.isAppOfArity ``List.cons 3 do return none
    let ke ← whnfR (l.getArg! 1)
    unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
    let some a ← fvKey (ke.getArg! 1) | return none
    let some b ← fvElem (ke.getArg! 2) | return none
    let some c ← fvKEs (l.getArg! 2) | return none
    return some (a ++ b ++ c)
  fvKey (k : Lean.Expr) : MetaM (Option (List String)) := do
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
  fvElem (el : Lean.Expr) : MetaM (Option (List String)) := do
    let el ← whnfR el
    match el.getAppFn.constName? with
    | some ``Perennial.Element.ElementExpression => fvOf (el.getArg! 2)
    | some ``Perennial.Element.ElementLiteralValue => fvKEs (el.getArg! 1)
    | _ => return none

/-- A proof of `ClosedUnder S e` (`S` given as the literal `Se`), built from the
constructors of `e`; `none` if it cannot be built. Cached on `(Se, e)`. -/
partial def closedPf (ext : Lean.Expr) (S : List String) (Se : Lean.Expr) (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if let some r := (← closedCache.get)[(Se, e)]? then return r
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
  let r ← do
    if e.isAppOfArity ``fvClosed 3 then
      -- a nested annotation: its own proof, and the inclusion of its set
      let Te := e.getArg! 1; let b := e.getArg! 2
      let some T ← strList? Te | pure none
      let some hb ← closedPf ext T Te b | pure none
      hoistCandidates.modify (·.push hb)
      let some hsub ← subsetPf T Te | pure none
      pure (some (lem ``closed_fv #[Te, b, hb, hsub]))
    else
    let e ← whnfR e
    let args := e.getAppArgs
    let rec' (x : Lean.Expr) := closedPf ext S Se x
    match e.getAppFn.constName? with
    | some ``Perennial.Expr.Val => pure (some (lem ``closed_val #[args[1]!]))
    | some ``Perennial.Expr.Var =>
      match ← strLit? args[1]! with
      | some y => match ← memPf y S Se with
        | some h => pure (some (lem ``closed_var #[args[1]!, h]))
        | none => pure none
      | none => pure none
    | some ``Perennial.Expr.Rec =>
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
    | some ``Perennial.Expr.App =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_app #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.Expr.If =>
      match ← rec' args[1]!, ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb, some hc =>
        pure (some (lem ``closed_if #[args[1]!, args[2]!, args[3]!, ha, hb, hc]))
      | _, _, _ => pure none
    | some ``Perennial.Expr.Pair =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_pair #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.Expr.Fst => return (← rec' args[1]!).map (lem ``closed_fst #[args[1]!, ·])
    | some ``Perennial.Expr.Snd => return (← rec' args[1]!).map (lem ``closed_snd #[args[1]!, ·])
    | some ``Perennial.Expr.Fork => return (← rec' args[1]!).map (lem ``closed_fork #[args[1]!, ·])
    | some ``Perennial.Expr.Primitive0 => pure (some (lem ``closed_prim0 #[args[1]!]))
    | some ``Perennial.Expr.Primitive1 =>
      return (← rec' args[2]!).map (lem ``closed_prim1 #[args[1]!, args[2]!, ·])
    | some ``Perennial.Expr.Primitive2 =>
      match ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb => pure (some (lem ``closed_prim2 #[args[1]!, args[2]!, args[3]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.Expr.ExternalOp =>
      return (← rec' args[2]!).map (lem ``closed_extop #[args[1]!, args[2]!, ·])
    | some ``Perennial.Expr.CmpXchg =>
      match ← rec' args[1]!, ← rec' args[2]!, ← rec' args[3]! with
      | some ha, some hb, some hc =>
        pure (some (lem ``closed_cmpxchg #[args[1]!, args[2]!, args[3]!, ha, hb, hc]))
      | _, _, _ => pure none
    | some ``Perennial.Expr.NewProph => pure (some (lem ``closed_newproph #[]))
    | some ``Perennial.Expr.ResolveProph =>
      match ← rec' args[1]!, ← rec' args[2]! with
      | some ha, some hb => pure (some (lem ``closed_resolve #[args[1]!, args[2]!, ha, hb]))
      | _, _ => pure none
    | some ``Perennial.Expr.LiteralValue =>
      return (← closedKEs args[1]!).map (lem ``closed_litval #[args[1]!, ·])
    | _ => pure none
  closedCache.modify (·.insert (Se, e) r)
  return r
where
  subsetPf (T : List String) (Te : Lean.Expr) : MetaM (Option Lean.Expr) := do
    match T with
    | [] => return some (mkApp2 (mkConst ``subset_nil) ext Se)
    | a :: t =>
      let Te' ← whnfR Te
      let tl := Te'.getArg! 2
      let some h1 ← memPf a S Se | return none
      let some h2 ← subsetPf t tl | return none
      return some (mkAppN (mkConst ``subset_cons) #[ext, Se, mkStrLit a, tl, h1, h2])
  closedKEs (l : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
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
  closedKey (k : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
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
  closedElem (el : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, Se] ++ args)
    let el ← whnfR el
    match el.getAppFn.constName? with
    | some ``Perennial.Element.ElementExpression =>
      return (← closedPf ext S Se (el.getArg! 2)).map (lem ``closed_el_expr #[el.getArg! 1, el.getArg! 2, ·])
    | some ``Perennial.Element.ElementLiteralValue =>
      return (← closedKEs (el.getArg! 1)).map (lem ``closed_el_lv #[el.getArg! 1, ·])
    | _ => return none

mutual

/-- `subst x v e` with a proof `subst x v e = e'` built from per-constructor lemmas
(non-constructor subterms are left as `subst x v _`, proved by `rfl`). -/
partial def substPf (ext : Lean.Expr) (x : String) (xe v : Lean.Expr) (dirty : IO.Ref Bool) (e : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  -- a closedness annotation `fvClosed S b`
  if e.isAppOfArity ``fvClosed 3 then
    let Se := e.getArg! 1; let b := e.getArg! 2
    if let some S ← strList? Se then
      if !S.contains x then
        if let some h ← closedPf ext S Se b then
          hoistCandidates.modify (·.push h)
          return (e, mkAppN (mkConst ``subst_pf_fvClosed) #[ext, Se, xe, v, b, h, notMemPf ext x xe S])
      -- `x` may occur: substitute into the body (definitionally the same), keeping
      -- the annotation with `x` removed
      let (b', pb) ← substPf ext x xe v dirty b
      let S' := S.filter (· != x)
      return (mkApp3 (mkConst ``fvClosed) ext (strListExpr S') b', pb)
  let e ← whnfR e
  let substE (e : Lean.Expr) := mkApp4 (mkConst ``Perennial.subst) ext xe v e
  let fallback : MetaM (Lean.Expr × Lean.Expr) := do
    dirty.set true
    let s := substE e
    return (s, ← mkEqRefl s)
  let rec' := substPf ext x xe v dirty
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Perennial.Expr.Val, #[_, w] => return (e, lem ``subst_pf_val #[w])
  | some ``Perennial.Expr.Var, #[_, y] =>
    match ← strLit? y with
    | some y' =>
      if y' == x then return (mk ``Perennial.Expr.Val #[v], lem ``subst_pf_var_eq #[])
      else return (e, lem ``subst_pf_var_ne #[y, strNeProof x y' xe y])
    | none => fallback
  | some ``Perennial.Expr.Rec, #[_, f, y, body] =>
    match ← binderLit? f, ← binderLit? y with
    | some fb, some yb =>
      if fb == some x then return (e, lem ``subst_pf_rec_f #[y, body])
      if yb == some x then return (e, lem ``subst_pf_rec_y #[f, body])
      let (body', pb) ← rec' body
      let f ← whnfR f; let y ← whnfR y
      let hf := binderNeProof ext x xe fb f
      let hy := binderNeProof ext x xe yb y
      return (mk ``Perennial.Expr.Rec #[f, y, body'], lem ``subst_pf_rec #[f, y, body, body', hf, hy, pb])
    | _, _ => fallback
  | some ``Perennial.Expr.App, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.Expr.App #[a', b'], lem ``subst_pf_app #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.If, #[_, a, b, c] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b; let (c', pc) ← rec' c
    return (mk ``Perennial.Expr.If #[a', b', c'], lem ``subst_pf_if #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.Expr.Pair, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.Expr.Pair #[a', b'], lem ``subst_pf_pair #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.Fst, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.Expr.Fst #[a'], lem ``subst_pf_fst #[a, a', pa])
  | some ``Perennial.Expr.Snd, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.Expr.Snd #[a'], lem ``subst_pf_snd #[a, a', pa])
  | some ``Perennial.Expr.Fork, #[_, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.Expr.Fork #[a'], lem ``subst_pf_fork #[a, a', pa])
  | some ``Perennial.Expr.Primitive0, #[_, op] => return (e, lem ``subst_pf_prim0 #[op])
  | some ``Perennial.Expr.Primitive1, #[_, op, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.Expr.Primitive1 #[op, a'], lem ``subst_pf_prim1 #[op, a, a', pa])
  | some ``Perennial.Expr.Primitive2, #[_, op, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.Expr.Primitive2 #[op, a', b'], lem ``subst_pf_prim2 #[op, a, b, a', b', pa, pb])
  | some ``Perennial.Expr.ExternalOp, #[_, op, a] =>
    let (a', pa) ← rec' a
    return (mk ``Perennial.Expr.ExternalOp #[op, a'], lem ``subst_pf_extop #[op, a, a', pa])
  | some ``Perennial.Expr.CmpXchg, #[_, a, b, c] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b; let (c', pc) ← rec' c
    return (mk ``Perennial.Expr.CmpXchg #[a', b', c'], lem ``subst_pf_cmpxchg #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.Expr.NewProph, #[_] => return (e, lem ``subst_pf_newproph #[])
  | some ``Perennial.Expr.ResolveProph, #[_, a, b] =>
    let (a', pa) ← rec' a; let (b', pb) ← rec' b
    return (mk ``Perennial.Expr.ResolveProph #[a', b'], lem ``subst_pf_resolve #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.LiteralValue, #[_, l] =>
    match ← substKEsPf ext x xe v dirty l with
    | some (l', pl) =>
      return (mk ``Perennial.Expr.LiteralValue #[l'], lem ``subst_pf_litval #[l, l', pl])
    | none => fallback
  | _, _ => fallback

/-- `substKeyedElements x v l` with a proof, for a list `l` built from constructors
(`none` otherwise). -/
partial def substKEsPf (ext : Lean.Expr) (x : String) (xe v : Lean.Expr) (dirty : IO.Ref Bool) (l : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  let l ← whnfR l
  if l.isAppOfArity ``List.nil 1 then return some (l, lem ``subst_pf_kes_nil #[])
  unless l.isAppOfArity ``List.cons 3 do return none
  let ke := l.getArg! 1; let tl := l.getArg! 2
  let some (ke', p1) ← substKEPf ext x xe v dirty ke | return none
  let some (tl', p2) ← substKEsPf ext x xe v dirty tl | return none
  return some (mkApp3 (mkConst ``List.cons [0]) (l.getArg! 0) ke' tl',
    lem ``subst_pf_kes_cons #[ke, ke', tl, tl', p1, p2])

/-- `substKeyedElement x v ke` with a proof (see `substKEsPf`). -/
partial def substKEPf (ext : Lean.Expr) (x : String) (xe v : Lean.Expr) (dirty : IO.Ref Bool) (ke : Lean.Expr) :
    MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, xe, v] ++ args)
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let ke ← whnfR ke
  unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
  let k ← whnfR (ke.getArg! 1)
  let el ← whnfR (ke.getArg! 2)
  let key? : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    if k.isAppOfArity ``Option.none 1 then return some (k, lem ``subst_pf_okey_none #[])
    unless k.isAppOfArity ``Option.some 2 do return none
    let kk ← whnfR (k.getArg! 1)
    let some' (e : Lean.Expr) := mkApp2 (mkConst ``Option.some [0]) (k.getArg! 0) e
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
  let elem? : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match el.getAppFn.constName?, el.getAppArgs with
    | some ``Perennial.Element.ElementExpression, #[_, t, e] =>
      let (e', pe) ← substPf ext x xe v dirty e
      return some (mk ``Perennial.Element.ElementExpression #[t, e'],
        lem ``subst_pf_el_expr #[t, e, e', pe])
    | some ``Perennial.Element.ElementLiteralValue, #[_, l] =>
      let some (l', pl) ← substKEsPf ext x xe v dirty l | return none
      return some (mk ``Perennial.Element.ElementLiteralValue #[l'],
        lem ``subst_pf_el_lv #[l, l', pl])
    | _, _ => return none
  let some (k', p1) ← key? | return none
  let some (el', p2) ← elem? | return none
  return some (mk ``Perennial.keyed_element.KeyedElement #[k', el'],
    lem ``subst_pf_ke #[k, k', el, el', p1, p2])

end

/-! ### Substitution of an environment (meta level)

Used to step through a run of `let:`s of values at once (`iWpLetRun?`). The
environment `σ` is a stack of layers (`envInsB b v` for a `let:`, `envDel b` under
a binder), newest first; the lookup of a variable walks the stack. -/

/-- A layer of an environment: `envInsB b v` (`ins`) or `envDel b` (`del`), with
the name of `b` (`none` for `BAnon`) and the binder `b` itself. -/
inductive EnvLayer where
  | ins (x : Option String) (b v : Lean.Expr)
  | del (x : Option String) (b : Lean.Expr)

/-- An environment: its layers (newest first, each with the environment below
it) and the environment expression. -/
structure MEnv where
  layers : List (EnvLayer × Lean.Expr)
  σ : Lean.Expr

/-- Push a layer. -/
def MEnv.push (ext : Lean.Expr) (env : MEnv) (l : EnvLayer) : MEnv :=
  let σ' := match l with
    | .ins _ b v => mkApp4 (mkConst ``envInsB) ext b v env.σ
    | .del _ b => mkApp3 (mkConst ``envDel) ext b env.σ
  { layers := (l, env.σ) :: env.layers, σ := σ' }

/-- The string literal of a binder `BNamed x`. -/
def binderStrExpr (b : Lean.Expr) : MetaM Lean.Expr := do
  return (← whnfR b).getArg! 0

/-- Look up `y` in the environment: the result (`some v`, or `none`) and a proof of
`σ y = result`. Cached on `(σ, y)`. -/
partial def envLookupPf (ext : Lean.Expr) (cache : IO.Ref (Std.HashMap (Lean.Expr × String) (Option Lean.Expr × Lean.Expr)))
    (y : String) (ye : Lean.Expr) (layers : List (EnvLayer × Lean.Expr)) (σ : Lean.Expr) :
    MetaM (Option Lean.Expr × Lean.Expr) := do
  if let some r := (← cache.get)[(σ, y)]? then return r
  let valTy := mkApp (mkConst ``Perennial.val) ext
  let optE (r : Option Lean.Expr) : Lean.Expr := match r with
    | some v => mkApp2 (mkConst ``Option.some [0]) valTy v
    | none => mkApp (mkConst ``Option.none [0]) valTy
  let r ← match layers with
    | [] => pure (none, mkApp2 (mkConst ``env_nil) ext ye)
    | (l, σ') :: rest =>
      match l with
      | .ins (some x) b v =>
        let xe ← binderStrExpr b
        if x == y then pure (some v, mkApp4 (mkConst ``env_insB_eq) ext xe v σ')
        else
          let (r, p) ← envLookupPf ext cache y ye rest σ'
          pure (r, mkAppN (mkConst ``env_insB_ne) #[ext, xe, ye, v, σ', optE r, strNeProof x y xe ye, p])
      | .ins none _ v =>
        let (r, p) ← envLookupPf ext cache y ye rest σ'
        pure (r, mkAppN (mkConst ``env_insB_anon) #[ext, ye, v, σ', optE r, p])
      | .del (some x) b =>
        let xe ← binderStrExpr b
        if x == y then pure (none, mkApp3 (mkConst ``env_del_named_eq) ext xe σ')
        else
          let (r, p) ← envLookupPf ext cache y ye rest σ'
          pure (r, mkAppN (mkConst ``env_del_named_ne) #[ext, xe, ye, σ', optE r, strNeProof x y xe ye, p])
      | .del none _ =>
        let (r, p) ← envLookupPf ext cache y ye rest σ'
        pure (r, mkAppN (mkConst ``env_del_anon) #[ext, ye, σ', optE r, p])
  cache.modify (·.insert (σ, y) r)
  return r

mutual

/-- `substEnv σ e` with a proof `substEnv σ e = e'`, for `e` built from
constructors (`none` otherwise). Closedness annotations `fvClosed S b` with no
variable of `S` bound by `σ` are kept as they are. -/
partial def substEnvPf (ext : Lean.Expr) (lcache : IO.Ref (Std.HashMap (Lean.Expr × String) (Option Lean.Expr × Lean.Expr)))
    (env : MEnv) (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let σ := env.σ
  let rec' := substEnvPf ext lcache env
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, σ] ++ args)
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  -- a closedness annotation `fvClosed S b`
  if e.isAppOfArity ``fvClosed 3 then
    let Se := e.getArg! 1; let b := e.getArg! 2
    if let some S ← strList? Se then
      -- the lookups of the variables of `S`
      let mut bound := false
      let mut lookups := #[]
      for s in S do
        let (r, p) ← envLookupPf ext lcache s (mkStrLit s) env.layers σ
        if r.isSome then bound := true
        lookups := lookups.push (s, r, p)
      if !bound then
        if let some h ← closedPf ext S Se b then
          hoistCandidates.modify (·.push h)
          -- `EnvAvoids S σ`
          let mut hσ := mkApp2 (mkConst ``env_avoids_nil) ext σ
          let mut tl := mkApp (mkConst ``List.nil [0]) (mkConst ``String)
          for (s, _, p) in lookups.reverse do
            hσ := mkAppN (mkConst ``env_avoids_cons) #[ext, σ, mkStrLit s, tl, p, hσ]
            tl := mkApp3 (mkConst ``List.cons [0]) (mkConst ``String) (mkStrLit s) tl
          return some (e, mkAppN (mkConst ``substEnv_pf_fvClosed) #[ext, Se, σ, b, h, hσ])
      -- some variable of `S` is bound: substitute into the body (definitionally the
      -- same), keeping the annotation with the bound variables removed
      let some (b', pb) ← rec' b | return none
      let S' := (lookups.filter (·.2.1.isNone)).toList.map (·.1)
      return some (mkApp3 (mkConst ``fvClosed) ext (strListExpr S') b', pb)
  let e ← whnfR e
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``Perennial.Expr.Val, #[_, w] => return some (e, lem ``substEnv_pf_val #[w])
  | some ``Perennial.Expr.Var, #[_, y] =>
    let some y' ← strLit? y | return none
    let (r, p) ← envLookupPf ext lcache y' y env.layers σ
    match r with
    | some w => return some (mk ``Perennial.Expr.Val #[w], lem ``substEnv_pf_var_some #[y, w, p])
    | none => return some (e, lem ``substEnv_pf_var_none #[y, p])
  | some ``Perennial.Expr.Rec, #[_, f, y, body] =>
    let some fb ← binderLit? f | return none
    let some yb ← binderLit? y | return none
    let f ← whnfR f; let y ← whnfR y
    let env' := (env.push ext (.del yb y)).push ext (.del fb f)
    let some (body', pb) ← substEnvPf ext lcache env' body | return none
    return some (mk ``Perennial.Expr.Rec #[f, y, body'], lem ``substEnv_pf_rec #[f, y, body, body', pb])
  | some ``Perennial.Expr.App, #[_, a, b] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    return some (mk ``Perennial.Expr.App #[a', b'], lem ``substEnv_pf_app #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.If, #[_, a, b, c] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    let some (c', pc) ← rec' c | return none
    return some (mk ``Perennial.Expr.If #[a', b', c'], lem ``substEnv_pf_if #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.Expr.Pair, #[_, a, b] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    return some (mk ``Perennial.Expr.Pair #[a', b'], lem ``substEnv_pf_pair #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.Fst, #[_, a] =>
    let some (a', pa) ← rec' a | return none
    return some (mk ``Perennial.Expr.Fst #[a'], lem ``substEnv_pf_fst #[a, a', pa])
  | some ``Perennial.Expr.Snd, #[_, a] =>
    let some (a', pa) ← rec' a | return none
    return some (mk ``Perennial.Expr.Snd #[a'], lem ``substEnv_pf_snd #[a, a', pa])
  | some ``Perennial.Expr.Fork, #[_, a] =>
    let some (a', pa) ← rec' a | return none
    return some (mk ``Perennial.Expr.Fork #[a'], lem ``substEnv_pf_fork #[a, a', pa])
  | some ``Perennial.Expr.Primitive0, #[_, op] => return some (e, lem ``substEnv_pf_prim0 #[op])
  | some ``Perennial.Expr.Primitive1, #[_, op, a] =>
    let some (a', pa) ← rec' a | return none
    return some (mk ``Perennial.Expr.Primitive1 #[op, a'], lem ``substEnv_pf_prim1 #[op, a, a', pa])
  | some ``Perennial.Expr.Primitive2, #[_, op, a, b] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    return some (mk ``Perennial.Expr.Primitive2 #[op, a', b'],
      lem ``substEnv_pf_prim2 #[op, a, b, a', b', pa, pb])
  | some ``Perennial.Expr.ExternalOp, #[_, op, a] =>
    let some (a', pa) ← rec' a | return none
    return some (mk ``Perennial.Expr.ExternalOp #[op, a'], lem ``substEnv_pf_extop #[op, a, a', pa])
  | some ``Perennial.Expr.CmpXchg, #[_, a, b, c] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    let some (c', pc) ← rec' c | return none
    return some (mk ``Perennial.Expr.CmpXchg #[a', b', c'],
      lem ``substEnv_pf_cmpxchg #[a, b, c, a', b', c', pa, pb, pc])
  | some ``Perennial.Expr.NewProph, #[_] => return some (e, lem ``substEnv_pf_newproph #[])
  | some ``Perennial.Expr.ResolveProph, #[_, a, b] =>
    let some (a', pa) ← rec' a | return none
    let some (b', pb) ← rec' b | return none
    return some (mk ``Perennial.Expr.ResolveProph #[a', b'], lem ``substEnv_pf_resolve #[a, b, a', b', pa, pb])
  | some ``Perennial.Expr.LiteralValue, #[_, l] =>
    let some (l', pl) ← substEnvKEsPf ext lcache env l | return none
    return some (mk ``Perennial.Expr.LiteralValue #[l'], lem ``substEnv_pf_litval #[l, l', pl])
  | _, _ => return none

/-- `substEnvKes σ l` with a proof (see `substEnvPf`). -/
partial def substEnvKEsPf (ext : Lean.Expr) (lcache : IO.Ref (Std.HashMap (Lean.Expr × String) (Option Lean.Expr × Lean.Expr)))
    (env : MEnv) (l : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, env.σ] ++ args)
  let l ← whnfR l
  if l.isAppOfArity ``List.nil 1 then return some (l, lem ``substEnv_pf_kes_nil #[])
  unless l.isAppOfArity ``List.cons 3 do return none
  let ke := l.getArg! 1; let tl := l.getArg! 2
  let some (ke', p1) ← substEnvKEPf ext lcache env ke | return none
  let some (tl', p2) ← substEnvKEsPf ext lcache env tl | return none
  return some (mkApp3 (mkConst ``List.cons [0]) (l.getArg! 0) ke' tl',
    lem ``substEnv_pf_kes_cons #[ke, ke', tl, tl', p1, p2])

/-- `substEnvKe σ ke` with a proof (see `substEnvPf`). -/
partial def substEnvKEPf (ext : Lean.Expr) (lcache : IO.Ref (Std.HashMap (Lean.Expr × String) (Option Lean.Expr × Lean.Expr)))
    (env : MEnv) (ke : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let lem (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext, env.σ] ++ args)
  let mk (n : Name) (args : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) (#[ext] ++ args)
  let ke ← whnfR ke
  unless ke.isAppOfArity ``Perennial.keyed_element.KeyedElement 3 do return none
  let k ← whnfR (ke.getArg! 1)
  let el ← whnfR (ke.getArg! 2)
  let key? : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    if k.isAppOfArity ``Option.none 1 then return some (k, lem ``substEnv_pf_okey_none #[])
    unless k.isAppOfArity ``Option.some 2 do return none
    let kk ← whnfR (k.getArg! 1)
    let some' (e : Lean.Expr) := mkApp2 (mkConst ``Option.some [0]) (k.getArg! 0) e
    match kk.getAppFn.constName?, kk.getAppArgs with
    | some ``Perennial.key.KeyField, #[_, f] => return some (k, lem ``substEnv_pf_okey_field #[f])
    | some ``Perennial.key.KeyInteger, #[_, i] => return some (k, lem ``substEnv_pf_okey_int #[i])
    | some ``Perennial.key.KeyExpression, #[_, t, e] =>
      let some (e', pe) ← substEnvPf ext lcache env e | return none
      return some (some' (mk ``Perennial.key.KeyExpression #[t, e']),
        lem ``substEnv_pf_okey_expr #[t, e, e', pe])
    | some ``Perennial.key.KeyLiteralValue, #[_, l] =>
      let some (l', pl) ← substEnvKEsPf ext lcache env l | return none
      return some (some' (mk ``Perennial.key.KeyLiteralValue #[l']),
        lem ``substEnv_pf_okey_lv #[l, l', pl])
    | _, _ => return none
  let elem? : MetaM (Option (Lean.Expr × Lean.Expr)) := do
    match el.getAppFn.constName?, el.getAppArgs with
    | some ``Perennial.Element.ElementExpression, #[_, t, e] =>
      let some (e', pe) ← substEnvPf ext lcache env e | return none
      return some (mk ``Perennial.Element.ElementExpression #[t, e'],
        lem ``substEnv_pf_el_expr #[t, e, e', pe])
    | some ``Perennial.Element.ElementLiteralValue, #[_, l] =>
      let some (l', pl) ← substEnvKEsPf ext lcache env l | return none
      return some (mk ``Perennial.Element.ElementLiteralValue #[l'],
        lem ``substEnv_pf_el_lv #[l, l', pl])
    | _, _ => return none
  let some (k', p1) ← key? | return none
  let some (el', p2) ← elem? | return none
  return some (mk ``Perennial.keyed_element.KeyedElement #[k', el'],
    lem ``substEnv_pf_ke #[k, k', el, el', p1, p2])

end

/-- Annotate the continuations (bodies of `let:`/`;;` lambdas and of the
`exceptionSeq` continuation) of a large expression with their free variables
(`fvClosed`); the result is definitionally equal to `e`. -/
partial def annotateFv (ext : Lean.Expr) (e : Lean.Expr) : MetaM Lean.Expr := do
  let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr Lean.Expr)
  go cache e
where
  wrapRec (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (r : Lean.Expr) : MetaM Lean.Expr := do
    let r' ← whnfR r
    let_expr Perennial.Expr.Rec _ f y body := r' | go cache r
    let body' ← go cache body
    -- small bodies are not worth it, and very deep ones (e.g. long composite
    -- literals) would make the closedness proofs too deep
    if decide (body'.approxDepth.toNat < 6) then
      return mkApp4 (mkConst ``Perennial.Expr.Rec) ext f y body'
    match ← fvOf body' with
    | some S =>
      let ann := mkApp3 (mkConst ``fvClosed) ext (strListExpr S) body'
      hoistCandidates.modify (·.push ann)
      return mkApp4 (mkConst ``Perennial.Expr.Rec) ext f y ann
    | none => return mkApp4 (mkConst ``Perennial.Expr.Rec) ext f y body'
  go (cache : IO.Ref (Std.HashMap Lean.Expr Lean.Expr)) (e : Lean.Expr) : MetaM Lean.Expr := do
    if let some r := (← cache.get)[e]? then return r
    let e' ← whnfR e
    let r ← match_expr e' with
      | Perennial.Expr.App _ a b => do
        let a' ← whnfR a
        let isSeq := match_expr a' with
          | Perennial.Expr.Val _ c => c.getAppFn.isConstOf `Perennial.exceptionSeq
          | _ => false
        let isRec := a'.isAppOf ``Perennial.Expr.Rec
        let na ← if isRec then wrapRec cache a else go cache a
        let nb ← if isSeq && (← whnfR b).isAppOf ``Perennial.Expr.Rec then wrapRec cache b
          else go cache b
        pure (mkApp3 (mkConst ``Perennial.Expr.App) ext na nb)
      | Perennial.Expr.If _ a b c => do
        pure (mkApp4 (mkConst ``Perennial.Expr.If) ext (← go cache a) (← go cache b) (← go cache c))
      | Perennial.Expr.Pair _ a b => do
        pure (mkApp3 (mkConst ``Perennial.Expr.Pair) ext (← go cache a) (← go cache b))
      | _ => pure e
    cache.modify (·.insert e r)
    return r

/-- Remove the closedness annotations (definitionally). -/
partial def stripFvCore (e : Lean.Expr) : Lean.Expr :=
  e.replace fun s => if s.isAppOfArity ``fvClosed 3 then some (stripFvCore (s.getArg! 2)) else none

def stripFv (e : Lean.Expr) : Lean.Expr :=
  if (e.find? (·.isConstOf ``fvClosed)).isNone then e else stripFvCore e

theorem tac_goal_defeq {PROP : Type _} [BI PROP] {Δ P Q : PROP} (h : Δ ⊢ Q) (heq : P = Q) : Δ ⊢ P :=
  heq ▸ h

/-- Add the goal `hyps ⊢ goal` with the closedness annotations removed. -/
def addBIGoalStripped {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (goal : Q($prop)) (k : Q($prop) → ProofModeM Lean.Expr := addBIGoal hyps) :
    ProofModeM Lean.Expr := do
  let goal' := stripFv goal
  if goal' == goal then return ← k goal
  let h ← k goal'
  let heq ← mkExpectedTypeHint (← mkEqRefl goal) (← mkEq goal goal')
  mkAppNamed ``tac_goal_defeq
    [("PROP", prop), ("Δ", ehyps), ("P", goal), ("Q", goal'), ("!h", h), ("!heq", heq)]

/-- Evaluate the `subst'`/`subst` applications at the head of `e`, with a proof
(`none`: unchanged). `vals` collects the substituted values; `dirty` is set if
some `subst` could not be evaluated. -/
partial def evalSubstsPf (ext : Lean.Expr) (vals : IO.Ref (Array Lean.Expr)) (dirty : IO.Ref Bool)
    (e : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  let e ← instantiateMVars e
  let orRefl (e : Lean.Expr) (p? : Option Lean.Expr) : MetaM Lean.Expr := match p? with
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
def simpReduct (ext : Lean.Expr) (K : List Lean.Expr) (e2 : Lean.Expr) (known : Array Lean.Expr := #[]) :
    MetaM (Lean.Expr × Option Lean.Expr) := do
  let vals ← IO.mkRef #[]
  let dirty ← IO.mkRef false
  let (e2s, p1?) ← evalSubstsPf ext vals dirty e2
  let vals ← vals.get
  let needs ← if !vals.isEmpty && !(← dirty.get) then vals.anyM needsGooseSimp
    else needsGooseSimp e2s known
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
    let exprTy := mkApp (mkConst ``Perennial.Expr) ext
    let f ← withLocalDeclD `x exprTy fun x => do mkLambdaFVars #[x] (← fillExpr K x)
    return (filled, some (← mkCongrArg f p))

/-- `(modality_laterN 1)` at the given BI. -/
def laterModality {u} (prop : Q(Type u)) (bi : Q(BI $prop)) : MetaM Q(Modality $prop $prop) :=
  mkAppOptM ``modality_laterN #[some prop, some (mkNatLit 1), some bi]

initialize laterCache : IO.Ref (Std.HashMap Lean.Expr Bool) ← IO.mkRef {}

/-- May `IntoLaterN` strip a later from (a part of) `ty`? A syntactic over-approximation:
`ty` has a `▷` or `▷^[n]` that is not below a wand or an implication. (No
`IntoLaterN` instance looks below `-∗`/`→`, so a `▷` there, as in a Löb induction hypothesis
whose own `▷` has been stripped or in a Texan-triple specification `∀ Φ, P -∗ ▷ (Q -∗ Φ) -∗
WP ...`, does not trigger the `IntoLaterN` search over all hypotheses on every step.) -/
def strippableLater (ty : Lean.Expr) : Bool :=
  (ty.findExt? fun s =>
    if s.isAppOf ``BIBase.later || s.isAppOf ``BIBase.laterN then .found
    else if s.isAppOf ``BIBase.wand || s.isAppOf ``BIBase.imp then .done
    else .visit).isSome

/-- Does some hypothesis have a later that `IntoLaterN` may strip (`strippableLater`)?
(Cached per hypothesis type and per context.) -/
partial def hypsHaveLater {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {e} (hyps : Hyps bi e) :
    MetaM Bool := do
  match hyps with
  | .emp _ => return false
  | .sep _ _ _ _ lhs rhs =>
    -- (cached per context, so that a step that adds a hypothesis costs `O(1)`)
    let e : Lean.Expr := e
    if e.hasMVar then return (← hypsHaveLater rhs) || (← hypsHaveLater lhs)
    if let some b := (← laterCache.get)[e]? then return b
    let b := (← hypsHaveLater rhs) || (← hypsHaveLater lhs)
    laterCache.modify fun c => (if c.size > 100000 then {} else c).insert e b
    return b
  | .hyp _ _ _ _ ty _ =>
    let ty ← instantiateMVars ty
    if let some b := (← laterCache.get)[ty]? then return b
    let b := strippableLater ty
    laterCache.modify fun c => (if c.size > 100000 then {} else c).insert ty b
    return b

/-- Introduce a `▷` in front of the hypotheses: `hyps ⊢ ▷ hyps'`, stripping laters
from the hypotheses. When no hypothesis has a strippable `▷`,
this is `later_intro` (`hyps' = hyps`), avoiding a typeclass search per
hypothesis on every step. -/
def iLaterIntro {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) : ProofModeM ((e' : Q($prop)) × Hyps bi e' × Lean.Expr) := do
  if ← hypsHaveLater hyps then
    let ⟨e', hyps', pf⟩ ← iModAction (prop1 := prop) (bi1 := bi) hyps (← laterModality prop bi)
    return ⟨e', hyps', pf⟩
  -- (`▷` rather than `▷^[1]`, as in the tactic lemmas: no unfolding in the kernel)
  let pf ← mkAppOptM ``BI.later_intro #[some prop, some bi, some ehyps]
  return ⟨ehyps, hyps, pf⟩

/-- Is `e` an application of a `CompositeLiteral` instruction (possibly curried)? -/
def isCompositeLitApp (e : Lean.Expr) : MetaM Bool := do
  let mut e ← whnfR e
  for _ in [0:4] do
    let_expr Perennial.Expr.App _ f _ := e | return false
    if let some fv ← isGooseVal? f then
      let fv ← whnfR fv
      let_expr Perennial.val.GoInstruction _ i := fv | return false
      return (← whnfR i).isAppOf ``GoInstruction.CompositeLiteral
    e ← whnfR f
  return false

/-- Find the pure step that `iWpPureStep` would take (the outermost redex with a
`PureWp` instance satisfying `pred`) and solve its side condition. -/
def iWpPureStepFind (wp : GooseWpGoal) (failOnUnsolved : Bool)
    (pred : Lean.Expr → MetaM Bool := fun _ => pure true) (multi : Bool := false) :
    ProofModeM (PureStep × Lean.Expr) := do
  let gs ← gooseGSArgs wp.ι
  let stepSliceLits := (goose.wp.unfoldSliceLiterals.get (← getOptions)).or
    (!goose.wp.extras.get (← getOptions))
  let some (st, _, _) ← findEctx wp.e (fun K e1 => do
      unless ← pred e1 do throwError "skip"
      -- a head redex has values in its evaluation positions (all `PureWp`
      -- instances are of this form): skip the (costly) instance search otherwise
      -- (instances may match curried applications `App (App (Val f) (Val v1)) (Val v2)`)
      if let some (_, hole) ← extractEctxItem e1 then
        let rec valApp (fuel : Nat) (h : Lean.Expr) : MetaM Bool := do
          if (← isGooseVal? h).isSome then return true
          match fuel with
          | 0 => return false
          | fuel + 1 =>
            let h ← whnfR h
            let_expr Perennial.Expr.App _ f a := h | return false
            return (← valApp fuel a) && (← valApp fuel f)
        -- (only an application can be a redex with an application of values in
        -- evaluation position, e.g. not `(#l, #x +⟨t⟩ #y)`; and an application
        -- whose function is not a value or a curried application of values, e.g.
        -- `(rec: ...) (f #v)`, is not one either)
        let e1' ← whnfR e1
        if e1'.isAppOfArity ``Perennial.Expr.App 3 then
          unless ← valApp 8 hole do throwError "skip"
          unless ← valApp 8 (e1'.getArg! 1) do throwError "skip"
        else
          unless (← isGooseVal? hole).isSome do throwError "skip"
      let some (φ, e2, inst) ← synthPureWp gs e1 | throwError "no PureWp instance"
      -- `wp_pures`/`wp_auto` stop at slice composite literals
      -- (`go.composite_literal_slice` is not an instance): use `wp_slice_literal`
      if multi && !stepSliceLits then
        -- (only composite literals: the instance of e.g. a beta step contains the
        -- whole function body, which is not worth traversing)
        if ← isCompositeLitApp e1 then
          if (← instantiateMVars inst).getUsedConstants.contains
              `Perennial.go.SliceSemantics.composite_literal_slice then
            throwError "slice literal"
      return ({ K, e1, φ, e2, inst } : PureStep))
    | throwIPMError "could not find a head subexpression with a known next step"
  let hφ ← solvePureSideCondition st.φ failOnUnsolved
  return (st, hφ)

/-- The subterms of the redex `e1` up to depth 3 (looking through reducible
definitions such as `Let`): these are parts of the WP expression, hence in
`goose_wp_simp` normal form, and a step that only moves them (e.g. `Rec` to
`RecV`, or a beta step for an anonymous binder) need not re-check them. -/
def redexParts (e1 : Lean.Expr) : MetaM (Array Lean.Expr) := do
  let rec go : Nat → Lean.Expr → Array Lean.Expr → MetaM (Array Lean.Expr)
    | 0, _, acc => pure acc
    | d + 1, e, acc => do
      let mut acc := acc
      for a in (← whnfR e).getAppArgs do
        acc ← go d a (acc.push a)
      return acc
  go 3 e1 #[]

/-- Take the pure step `st` found by `iWpPureStepFind`. -/
def iWpPureStepTake {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (st : PureStep) (hφ : Lean.Expr) (lc : Bool) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let ⟨ehyps', hyps', hlater⟩ ← iLaterIntro hyps
  -- the subterms of the redex are in normal form (as parts of the WP expression)
  let known ← redexParts st.e1
  let (e', heq?) ← simpReduct wp.ext st.K (← instantiateMVars st.e2) known
  let heq ← wp.wrapEq e' heq?
  let Kq := wp.quoteK st.K
  let gs ← gooseGSArgs wp.ι
  if !lc && gs.size == 9 then
    -- built directly (`tac_wp_pure_wp'` takes the 9 section variables of `gs` first)
    let k := fun (h : Lean.Expr) => pure <| mkAppN (mkConst ``tac_wp_pure_wp')
      (gs ++ #[st.φ, st.e1, st.e2, wp.wrap e', st.inst, Kq, ehyps, ehyps', wp.s, wp.E, wp.Φ,
        hφ, hlater, heq, h])
    return ⟨ehyps', hyps', e', k⟩
  let k := fun (h : Lean.Expr) => wp.mkAppNamed (if lc then ``tac_wp_pure_wp_lc' else ``tac_wp_pure_wp')
    [("Δ", ehyps), ("Δ'", ehyps'), ("e2", st.e2), ("e'", wp.wrap e'),
     ("Hwp", st.inst), ("K", Kq), ("e1", st.e1), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ),
     ("hφ", hφ), ("hlater", hlater), ("!heq", heq),
     (if lc then "h" else "!h", h)]
  return ⟨ehyps', hyps', e', k⟩

/-- Take one pure step in the WP goal `hyps ⊢ wp`. Returns the new context,
the new (simplified) expression, and a function turning a proof of the new goal
(`hyps' ⊢ WP e' ...`, or `hyps' ⊢ £ 1 -∗ WP e' ...` when `lc`) into a proof of
the old one. `pred` restricts the redexes considered. -/
def iWpPureStep {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (failOnUnsolved lc : Bool)
    (pred : Lean.Expr → MetaM Bool := fun _ => pure true) :
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let (st, hφ) ← iWpPureStepFind wp failOnUnsolved pred
  iWpPureStepTake hyps wp st hφ lc

register_option goose.wp.letRun : Nat := {
  defValue := 2
  descr := "the minimal length of a run of `let:`s of values that `wp_pures`/`wp_auto` step \
    through at once, substituting an environment into the body after the run once \
    (`tac_wp_let_env`); 0 disables this"
}

/-- A `let:` (or `;;`) of a value: `App (Rec BAnon b body) (Val v)`, possibly under a
closedness annotation; returns `(b, name of b, v, body)`. -/
def valueLet? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Option String × Lean.Expr × Lean.Expr)) := do
  let e ← whnfR e
  let_expr Perennial.Expr.App _ f a := e | return none
  let f ← whnfR f
  let_expr Perennial.Expr.Rec _ fb b body := f | return none
  unless (← whnfR fb).isConstOf ``Binder.BAnon do return none
  let some bl ← binderLit? b | return none
  let some v ← isGooseVal? a | return none
  return some (← whnfR b, bl, v, body)

/-- The evaluation context `K` (innermost first) and the run of `let:`s of values
`(b, name, v, body)` at the head of the WP expression `e`, if there is one. -/
def findLetRun (e : Lean.Expr) :
    MetaM (Option (List Lean.Expr × Lean.Expr × Array (Lean.Expr × Option String × Lean.Expr × Lean.Expr))) := do
  let mut cur := e
  let mut K := []
  for _ in [0:64] do
    if let some l ← valueLet? cur then
      let mut run := #[l]
      let mut body := l.2.2.2
      repeat
        let some l ← valueLet? body | break
        run := run.push l
        body := l.2.2.2
      return some (K, cur, run)
    let some (Ki, h) ← extractEctxItem cur | return none
    if (← isGooseVal? h).isSome then return none
    K := Ki :: K
    cur := h
  return none

/-- Step through a run of at least `goose.wp.letRun` `let:`s of values at the head of
the WP goal `hyps ⊢ wp` at once (`tac_wp_let_env`; two pure steps per `let:`, each
introducing a `▷` as `iLaterIntro`). Returns the new context, the new expression,
and a function turning a proof of the new goal into a proof
of the old one; `none` if there is no such run, or if the body after the run is not
built from constructors. -/
def iWpLetRun? {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) :
    ProofModeM (Option ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr))) := do
  let minRun := goose.wp.letRun.get (← getOptions)
  if minRun == 0 then return none
  let some (K, c0, run) ← findLetRun wp.e | return none
  if run.size < minRun then return none
  let ext := wp.ext
  -- the environments `σ₀ = envNil, ..., σₖ`
  let mut env : MEnv := { layers := [], σ := mkApp (mkConst ``envNil) ext }
  let mut sigmas := #[env.σ]
  for (b, bl, v, _) in run do
    env := env.push ext (.ins bl b v)
    sigmas := sigmas.push env.σ
  let body := run.back!.2.2.2
  let lcache ← IO.mkRef {}
  let some (body', pbody) ← substEnvPf ext lcache env body | return none
  -- as `simpReduct`: the body is in `goose_wp_simp` normal form, only the substituted
  -- values may not be
  let (body', pbody) ← if ← run.anyM (needsGooseSimp ·.2.2.1) then
      match ← gooseExprSimp body' with
      | (body'', some p2) => pure (body'', ← mkEqTrans pbody p2)
      | (body'', none) => pure (body'', pbody)
    else pure (body', pbody)
  -- the `▷`s of the steps
  let mut cur : (e : Q($prop)) × Hyps bi e := ⟨ehyps, hyps⟩
  let mut deltas := #[ehyps]
  let mut laters := #[]
  for _ in [0:2 * run.size] do
    let ⟨_, h⟩ := cur
    let ⟨e', h', pf⟩ ← iLaterIntro h
    cur := ⟨e', h'⟩
    deltas := deltas.push e'
    laters := laters.push pf
  let ⟨ehyps', hyps'⟩ := cur
  let e' ← fillExpr K body'
  let Kq := wp.quoteK K
  let gs ← gooseGSArgs wp.ι
  let exprTy := mkApp (mkConst ``Perennial.Expr) ext
  let k := fun (h : Lean.Expr) => do
    -- `Δ₂ₖ ⊢ WP (fill K (substEnv σₖ body))`
    let f ← withLocalDeclD `x exprTy fun x => do mkLambdaFVars #[x] (← fillExpr K x)
    let heq ← wp.wrapEq e' (some (← mkCongrArg f pbody))
    let mut pf ← wp.mkAppNamed ``tac_wp_expr_simp
      [("Δ", deltas[2 * run.size]!), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ),
       ("e", wp.wrap (← fillExpr K (mkApp3 (mkConst ``substEnv) ext sigmas[run.size]! body))),
       ("e'", wp.wrap e'), ("!h", h), ("!heq", heq)]
    -- the `let:`s, last first
    for i' in [0:run.size] do
      let i := run.size - 1 - i'
      let (b, _, v, bd) := run[i]!
      pf := mkAppN (mkConst ``tac_wp_let_env) (gs ++ #[sigmas[i]!, b, v, bd, Kq,
        deltas[2 * i]!, deltas[2 * i + 1]!, deltas[2 * i + 2]!, wp.s, wp.E, wp.Φ,
        laters[2 * i]!, laters[2 * i + 1]!, pf])
    return mkAppN (mkConst ``tac_wp_env_enter) (gs ++ #[c0, Kq, ehyps, wp.s, wp.E, wp.Φ, pf])
  return some ⟨ehyps', hyps', e', k⟩

/-- Simplify the expression of the WP goal with `goose_wp_simp`. Returns the new
(inner) expression and a function turning a proof of the new goal into a proof
of the old one, or `none` if nothing changed. -/
def iWpExprSimp (wp : GooseWpGoal) (Δ : Lean.Expr) : MetaM (Option (Lean.Expr × (Lean.Expr → MetaM Lean.Expr))) := do
  unless ← needsGooseSimp wp.e do return none
  let (e', p?) ← gooseExprSimp wp.e
  let some _ := p? | return none
  if e' == wp.e then return none
  let heq ← wp.wrapEq e' p?
  return some (e', fun h => wp.mkAppNamed ``tac_wp_expr_simp
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e), ("e'", wp.wrap e'),
     ("!h", h), ("!heq", heq)])

/-- A value constant in evaluation position: a subterm `Val c` (an immediate
argument of a subexpression in evaluation position) where `c` is an application
of a (non-irreducible, non-projection) definition whose unfolding is a value that
is not a function (`#x` or a `val` constructor other than `RecV`), e.g. a Go
package constant `def a : val := #(W64 3)`. Returns `(c, unfolding)`. -/
def findValConst (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let env ← getEnv
  -- a value constant `c`, or one inside `PairV`/`InjLV`/`InjRV`
  let rec check : Nat → Lean.Expr → MetaM (Option (Lean.Expr × Lean.Expr))
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
    let ok := c''.isAppOf ``GoGlobalContext.intoVal ||
      (match c''.getAppFn with
       | .const m _ => m != ``Perennial.val.RecV && (env.find? m).any (·.isCtor)
       | _ => false)
    return if ok then some (c, c') else none
  for (_, e') in ← allEctx e do
    let e' ← whnfR (← instantiateMVars e')
    for a in e'.getAppArgs do
      let a ← whnfR a
      let_expr Perennial.Expr.Val _ c := a | continue
      if let some r ← check 8 c then return some r
  return none

/-- Unfold one value constant in evaluation position (`findValConst`) in the WP
goal (definitional). Used by `wp_auto` when no other step applies. -/
def iWpUnfoldValConst? (wp : GooseWpGoal) (Δ : Lean.Expr) :
    MetaM (Option (Lean.Expr × (Lean.Expr → MetaM Lean.Expr))) := do
  let some (c, c') ← findValConst wp.e | return none
  let e' := wp.e.replace fun s => if s == c then some c' else none
  if e' == wp.e then return none
  let heq ← mkExpectedTypeHint (← mkEqRefl (wp.wrap wp.e)) (← mkEq (wp.wrap wp.e) (wp.wrap e'))
  return some (e', fun h => wp.mkAppNamed ``tac_wp_expr_simp
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("e", wp.wrap wp.e), ("e'", wp.wrap e'),
     ("!h", h), ("!heq", heq)])

/-- Turn the goal `hyps ⊢ WP (Val v) {{ Φ }}` into `hyps ⊢ Φ v` (by
`wp_value`), continuing with `k` on the new conclusion. -/
def iWpValue {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (v : Lean.Expr)
    (k : Lean.Expr → ProofModeM Lean.Expr) : ProofModeM Lean.Expr := do
  let goal := (mkApp wp.Φ v).headBeta
  let pf ← k goal
  wp.mkAppNamed ``tac_wp_value_nofupd
    [("Δ", ehyps), ("s", wp.s), ("E", wp.E), ("v", v), ("Φ", wp.Φ), ("!H", pf)]

/-! ### Focusing on a redex deep inside an evaluation context

When the redex of the WP expression is deep inside its evaluation context `K`
(e.g. in the code that loads or stores a wide struct field by field), every step
would cost `O(|K|)` (finding the redex, quoting `K`, and checking `fill K` in the
kernel). `wp_auto`/`wp_pures` then *focus*: `WP (fill K e) {{ Φ }}` becomes
`WP e {{ wpNestedPost K Φ }}` (`tac_wp_focus`), and when `e` becomes a value the
innermost item of `K` is popped. A goal that is returned to the user is
unfocused first (`tac_wp_unfocus`), so focusing is invisible. -/

/-- The evaluation-context depth from which the tactics focus, and the number of
items they keep around the redex. -/
def focusTrigger : Nat := 6
def focusMargin : Nat := 3

/-- The evaluation-context path of `e` (items and holes, outermost first), if it
is longer than `focusTrigger` (checked in `O(focusTrigger)` otherwise). -/
def deepEctxPath? (e : Lean.Expr) : MetaM (Option (Array (Lean.Expr × Lean.Expr))) := do
  let mut cur := e
  let mut acc := #[]
  for _ in [0:focusTrigger + 1] do
    let some (Ki, h) ← extractEctxItem cur | return none
    if (← isGooseVal? h).isSome then return none
    acc := acc.push (Ki, h)
    cur := h
  repeat
    let some (Ki, h) ← extractEctxItem cur | break
    if (← isGooseVal? h).isSome then break
    acc := acc.push (Ki, h)
    cur := h
  return some acc

/-- Focus on the redex of `wp` if it is deep in its evaluation context: the new
goal (expression and postcondition `wpNestedPost`), and a function turning a proof
of it into a proof of the old one. -/
def GooseWpGoal.focus? (wp : GooseWpGoal) (Δ : Lean.Expr) :
    MetaM (Option (GooseWpGoal × (Lean.Expr → MetaM Lean.Expr))) := do
  unless wp.tail.isNone do return none
  let some path ← deepEctxPath? wp.e | return none
  let cut := path.size - focusMargin
  -- the items outside the focus, innermost first
  let items := ((path.extract 0 cut).map (·.1)).reverse.toList
  let e' := path[cut - 1]!.2
  let Kq := quoteEctx wp.ext items
  let some Φ' ← mkAppNamedDirect? ``wpNestedPost
      ((← wp.ctxArgs) ++ [("s", wp.s), ("E", wp.E), ("K", Kq), ("Φ", wp.Φ)]) (partialApp := true)
    | return none
  return some ({ wp with e := e', Φ := Φ' }, fun h => wp.mkAppNamed ``tac_wp_focus
    [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("K", Kq), ("e", e'), ("Φ", wp.Φ), ("!h", h)])

/-- The arguments `(s, E, K, Φ)` of a postcondition `wpNestedPost s E K Φ`, and the
partial application to the section variables. -/
def nestedPostArgs? (Φ : Lean.Expr) : Option (Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr × Lean.Expr) :=
  let Φ := Φ.consumeMData
  if !Φ.getAppFn.isConstOf ``wpNestedPost then none else
  let args := Φ.getAppArgs
  let n := args.size
  if n < 4 then none else
  some (args[n-4]!, args[n-3]!, args[n-2]!, args[n-1]!, mkAppN Φ.getAppFn (args.extract 0 (n - 4)))

/-- The goal `wpNestedPost s E K Φ v` (after the focused expression became the value
`v`) with the innermost item `Ki` of `K = Ki :: K'` popped:
`WP (fillItem Ki (Val v)) @ s; E {{ wpNestedPost s E K' Φ }}`, or `Φ v` (popped
again if it is of this form) if `K = []` (definitionally equal). `none` if the goal is
not of this form. -/
partial def popNestedPost? (wp : GooseWpGoal) (goal : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let goal := goal.consumeMData
  unless goal.isApp do return none
  let some (s, E, K, Φ, head) := nestedPostArgs? goal.appFn! | return none
  let v := goal.appArg!
  let K' ← whnfR K
  if K'.isAppOfArity ``List.nil 1 then
    -- (`Φ` may again be a `wpNestedPost`, of an enclosing focus)
    let g := (mkApp Φ v).headBeta
    return some ((← popNestedPost? wp g).getD g)
  unless K'.isAppOfArity ``List.cons 3 do return none
  let e ← fillItemExpr (K'.getArg! 1) (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext v)
  return some ({ wp with s, E, tail := none }.mk' e (mkAppN head #[s, E, K'.getArg! 2, Φ]))

/-- A literal list of evaluation-context items. -/
partial def ectxListLit? (K : Lean.Expr) : MetaM (Option (List Lean.Expr)) := do
  let K ← whnfR K
  if K.isAppOfArity ``List.nil 1 then return some []
  unless K.isAppOfArity ``List.cons 3 do return none
  let some t ← ectxListLit? (K.getArg! 2) | return none
  return some (K.getArg! 1 :: t)

/-- Undo `GooseWpGoal.focus?` (one level): `WP e {{ wpNestedPost K Φ }}` becomes
`WP (fill K e) {{ Φ }}` with `fill K e` computed. -/
def GooseWpGoal.unfocus? (wp : GooseWpGoal) (Δ : Lean.Expr) :
    MetaM (Option (GooseWpGoal × (Lean.Expr → MetaM Lean.Expr))) := do
  unless wp.tail.isNone do return none
  let some (s, E, K, Φ, _) := nestedPostArgs? wp.Φ | return none
  let some items ← ectxListLit? K | return none
  let e' ← fillExpr items wp.e
  return some ({ wp with e := e', Φ }, fun h => wp.mkAppNamed ``tac_wp_unfocus
    [("Δ", Δ), ("s", s), ("E", E), ("K", K), ("e", wp.e), ("Φ", Φ), ("!h", h)])

/-- Add the goal `hyps ⊢ WP e {{ Φ }}` of `wp`, unfocused (`GooseWpGoal.unfocus?`). -/
partial def addWpGoal {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) : ProofModeM Lean.Expr := do
  if let some (wp', k) ← wp.unfocus? ehyps then return ← k (← addWpGoal hyps wp')
  addBIGoal hyps (wp.mk' wp.e wp.Φ)

/-- Repeatedly take pure steps (`wp_pures`); steps whose side condition cannot
be discharged automatically are not taken. When the expression becomes a value
`v`, the WP is replaced by `Φ v`, and if that is again a WP, stepping continues. -/
partial def iWpPures {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) (simpFirst : Bool := true) : ProofModeM Lean.Expr := do
  if simpFirst then
    if let some (e', k) ← iWpExprSimp wp ehyps then
      return ← k (← iWpPures hyps { wp with e := e' } (simpFirst := false))
  if let some v ← wp.isVal? then
    return ← iWpValue hyps wp v fun goal => do
      let goal := (← popNestedPost? wp goal).getD goal
      if let some wp' ← parseGooseWp? goal then iWpPures hyps wp'
      else addBIGoal hyps goal
  if let some (wp', k) ← wp.focus? ehyps then
    return ← k (← iWpPures hyps wp' (simpFirst := false))
  -- a run of `let:`s of values: step through it at once
  if let some (some ⟨_, hyps', e', k⟩) ← observing? (iWpLetRun? hyps wp) then
    return ← k (← iWpPures hyps' { wp with e := e' } (simpFirst := false))
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
      return ← addWpGoal hyps wp
    let pf ← iWpPures hyps' { wp with e := e' } (simpFirst := false)
    k pf
  | none => addWpGoal hyps wp

/-- Finish a goal `hyps ⊢ WP e {{ Φ }}`: if `e` is a value, replace the WP by
`Φ v`; otherwise leave it. -/
def iWpFinish {u} {prop : Q(Type u)} {bi : Q(BI $prop)} {ehyps : Q($prop)}
    (hyps : Hyps bi ehyps) (wp : GooseWpGoal) : ProofModeM Lean.Expr := do
  if let some v ← wp.isVal? then
    iWpValue hyps wp v (addBIGoal hyps ·)
  else
    addBIGoal hyps (wp.mk' wp.e wp.Φ)

/-- Bind the evaluation context `K` around `e'` in the goal
`Δ ⊢ WP (fill K e') {{ Φ }}`: `k` is given the new conclusion
`WP e' {{ v, WP (fill K (Val v)) {{ Φ }} }}` and must prove it from `Δ`. -/
def iWpBindCore (Δ : Lean.Expr) (wp : GooseWpGoal) (K : List Lean.Expr) (e' : Lean.Expr)
    (k : Lean.Expr → ProofModeM Lean.Expr) : ProofModeM Lean.Expr := do
  if K.isEmpty && wp.tail.isNone then return ← k (wp.mk' e' wp.Φ)
  let valTy := mkApp (mkConst ``Perennial.val) wp.ext
  let Φ' ← withLocalDeclD `v valTy fun v => do
    let filled ← fillExpr K (mkApp2 (mkConst ``Perennial.Expr.Val) wp.ext v)
    mkLambdaFVars #[v] (wp.mk' filled wp.Φ)
  let pf ← k ({ wp with tail := none }.mk' e' Φ')
  wp.mkAppNamed ``tac_wp_bind [("Δ", Δ), ("s", wp.s), ("E", wp.E), ("K", wp.quoteK K),
    ("e'", e'), ("Φ", wp.Φ), ("!H", pf)]

/-- The evaluation context to bind for the "next"
operation (a function call, possibly curried, or the innermost expression that
is not an evaluation-context constructor). -/
def findBindNext (e : Lean.Expr) : MetaM (Option (List Lean.Expr × Lean.Expr)) := do
  let mut bindCtx : Option (List Lean.Expr × Lean.Expr) := none
  let mut isCallSoFar := true
  let mut cur := e
  let mut K : List Lean.Expr := []
  repeat
    let cur' ← whnfR (← instantiateMVars cur)
    if cur'.isAppOf ``Perennial.Expr.Val then break
    let isAppVal ← match_expr cur' with
      | Perennial.Expr.App _ _ e2 => pure (← isGooseVal? e2).isSome
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
def gooseMatchesPattern (e p : Lean.Expr) : MetaM Bool := do
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
def elabGoosePattern (stx : Term) (ext : Lean.Expr) : TermElabM Lean.Expr := do
  let ty := mkApp (mkConst ``Perennial.Expr) ext
  let e ← Term.elabTermEnsuringType (← `(gl($stx))) ty
  Term.synthesizeSyntheticMVarsNoPostponing (ignoreStuckTC := true)
  instantiateMVars e

/-! ### Hoisting closed subterms out of binders

A proof built by `wp_auto` has a binder per allocation (the location), and the rest
of the function (its closedness annotations `fvClosed S e`, nested: each contains the
next one) and the closedness proofs of these annotations are referenced below a
growing number of them. These terms mention the section variables (`ext`, the
`GoGlobalContext`, ...), which the declaration abstracts as bound variables, so a
term shared at `k` binder depths is stored (and checked by the kernel) `k` times:
the proof had size `O(n²)` for `n` allocations. `assignHoisted` turns the proof into
`let h₁ := t₁; ...; let hₘ := tₘ; p`, where the `tᵢ` are these terms
(`hoistCandidates`, registered when they are built), each with the earlier `hⱼ`
replaced in it: each is then stored and checked once.

(The hypotheses of the proof mode context mention the locations, i.e. the bound
variables, so they cannot be hoisted: a context with `n` live points-to facts still
gives a proof of size `O(n²)`.) -/

/-- Replace the subterms of `e` in `map` (by pointer), except `e` itself. -/
unsafe def replacePtrs (map : PtrMap Lean.Expr Lean.Expr) (e : Lean.Expr) : Lean.Expr :=
  e.replace fun t => if ptrEq t e then none else map.find? t

/-- See "Hoisting closed subterms out of binders": the occurrences in `e` of the terms
`cands` (in creation order, by pointer) are replaced by `let`-bound variables, and the
free variables `zs` by `Rs`. `e` is fully instantiated. -/
unsafe def hoistClosedImpl (e : Lean.Expr) (cands : Array Lean.Expr) (zs Rs : Array Lean.Expr) :
    MetaM Lean.Expr := do
  if cands.isEmpty then return e.replaceFVars zs Rs
  -- (each candidate with the earlier ones replaced)
  let mut map : PtrMap Lean.Expr Lean.Expr := mkPtrMap
  let mut vals : Array (FVarId × Lean.Expr) := #[]
  for t in cands do
    if map.contains t then continue
    let v := replacePtrs map t
    let fvarId ← mkFreshFVarId
    map := map.insert t (mkFVar fvarId)
    vals := vals.push (fvarId, v)
  -- (a term less deep than all the candidates contains none of them)
  let minDepth := cands.foldl (fun d t => min d t.approxDepth) cands[0]!.approxDepth
  let body := e.replace fun t => if t.approxDepth < minDepth then some t else map.find? t
  let body := if zs.isEmpty then body else body.replaceFVars zs Rs
  -- the candidates that occur (possibly in another one that occurs)
  let mut need := (collectFVars {} body).fvarSet
  for i' in [0:vals.size] do
    let (fvarId, v) := vals[vals.size - 1 - i']!
    if need.contains fvarId then
      need := (collectFVars { fvarSet := need } v).fvarSet
  let mut lctx ← getLCtx
  let insts ← getLocalInstances
  let mut fvars := #[]
  for (fvarId, v) in vals do
    unless need.contains fvarId do continue
    let ty ← withLCtx lctx insts (inferType v)
    lctx := lctx.mkLetDecl fvarId `h ty v
    fvars := fvars.push (mkFVar fvarId)
  if fvars.isEmpty then return body
  withLCtx lctx insts (mkLetFVars fvars body (usedLetOnly := false))

@[implemented_by hoistClosedImpl]
opaque hoistClosed (e : Lean.Expr) (cands : Array Lean.Expr) (zs Rs : Array Lean.Expr) : MetaM Lean.Expr

/-- The number of steps that introduced a binder in the proof (allocations), for
`assignHoisted`. -/
initialize binderSteps : IO.Ref Nat ← IO.mkRef 0

/-- `assignHoisted` only hoists when there are at least this many binders. -/
def hoistMinBinders : Nat := 4

/-- Assign the goal `mvar` the proof `pf`, built by a tactic below binders (e.g.
allocations; `binderSteps`), with the closed terms `cands` hoisted out of the binders
(`hoistClosed`).

`pf` cannot be instantiated as it is: its remaining goals `?g` (`goals`, in contexts
with the variables `ys` of the binders, or with some variables cleared) block the
instantiation of the delayed assignments of the binders. They are temporarily
assigned `z ys`, for a new free variable `z : ∀ ys, T` (`T` the type of `?g`);
after instantiating and hoisting, `z` is replaced by a new metavariable `?R` of the
outer context, assigned `fun ys => ?g` (`?g` itself if there is no `ys`). -/
def assignHoisted (mvar : MVarId) (pf : Lean.Expr) (cands : Array Lean.Expr) (goals : Array MVarId) :
    MetaM Unit := do
  -- (with few binders, the duplication is small: not worth the traversals)
  if cands.isEmpty || (← binderSteps.get) < hoistMinBinders then
    mvar.assign pf
    return
  let outer ← mvar.getDecl
  let saved ← getMCtx
  -- the remaining goals: `(g, ys, z, type of z)`
  let mut pending : Array (MVarId × Array Lean.Expr × Lean.Expr × Lean.Expr) := #[]
  for g in goals do
    if ← g.isAssignedOrDelayedAssigned then continue
    let gd ← g.getDecl
    let ys := gd.lctx.foldl (init := #[]) fun acc d =>
      if outer.lctx.contains d.fvarId then acc else acc.push d.toExpr
    let T ← withLCtx gd.lctx gd.localInstances (mkForallFVars ys gd.type)
    let z := mkFVar (← mkFreshFVarId)
    g.assign (mkAppN z ys)
    pending := pending.push (g, ys, z, T)
  let P ← instantiateMVars pf
  setMCtx saved
  if P.hasExprMVar then
    -- (another metavariable blocks the instantiation)
    mvar.assign pf
    return
  let mut zs := #[]
  let mut Rs := #[]
  let mut lctx := outer.lctx
  for (g, ys, z, T) in pending do
    zs := zs.push z
    lctx := lctx.mkLocalDecl z.fvarId! `z T
    if ys.isEmpty then
      Rs := Rs.push (mkMVar g)
    else
      let R ← mkFreshExprMVarAt outer.lctx outer.localInstances T
      let gd ← g.getDecl
      R.mvarId!.assign (← withLCtx gd.lctx gd.localInstances (mkLambdaFVars ys (mkMVar g)))
      Rs := Rs.push R
  mvar.assign (← withLCtx lctx outer.localInstances (hoistClosed P cands zs Rs))
end tactics

/-! ## The tactics -/

open Lean Elab Tactic Meta Qq Iris.ProofMode in
/-- `wp_pures` takes all pure steps at the head of the WP goal: it repeatedly
finds the outermost subexpression in evaluation position that has a `PureWp`
instance (beta reduction, `if` on a literal boolean, projections of pairs, Go
instructions with a deterministic pure semantics, `exceptionSeq`, ...) and
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
      | none => Pure.pure (fun _ => Pure.pure true : Lean.Expr → MetaM Bool)
      | some pat => do
        let p ← elabGoosePattern pat wp.ext
        Pure.pure (fun e => withNewMCtxDepth (gooseMatchesPattern e p) : Lean.Expr → MetaM Bool)
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

`wp_bind` (no argument) focuses on the next
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- Call a function value `fv` that unfolds to
`rec: f x := e`. The recursive occurrences of `f` are replaced by the folded `fv`. -/
theorem tac_wp_call' {fv v2 : val} {f x : Binder} {e e' : Expr} (hfv : fv = RecV f x e)
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
    (hlater : Δ ⊢ ▷ Δ') (heq : fill K (subst' x v2 (subst' f fv e)) = e')
    (h : Δ' ⊢ WP e' @ s; E {{ Φ }}) :
    Δ ⊢ WP (fill K (App (Val fv) (Val v2))) @ s; E {{ Φ }} := by
  subst hfv
  exact tac_wp_pure_wp' (Hwp := wp_call (G := G) (L := L) v2 f x e) trivial hlater heq h

theorem tac_wp_call_lc' {fv v2 : val} {f x : Binder} {e e' : Expr} (hfv : fv = RecV f x e)
    {K : List EctxItem} {Δ Δ' : IProp GF} {s : Stuckness} {E : CoPset} {Φ : val → IProp GF}
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
    ProofModeM ((ehyps' : Q($prop)) × Hyps bi ehyps' × Lean.Expr × (Lean.Expr → MetaM Lean.Expr)) := do
  let some ((fv, v2, f, x, body), K, _) ← findEctx wp.e (fun _ e => do
      let e ← whnfR e
      let_expr Perennial.Expr.App _ e1 e2 := e | throwError "not an application"
      let some fv ← isGooseVal? e1 | throwError "not a value"
      let some v2 ← isGooseVal? e2 | throwError "not a value"
      -- `onlyImpl`: only implementation constants `Foo.impl`/`T.M.impl` (as produced by
      -- `wp_func_call`/`wp_method_call`)
      if onlyImpl then
        let some n := (← instantiateMVars fv).getAppFn.constName? | throwError "not a constant"
        unless n matches .str _ "impl" do
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
  let k := fun (h : Lean.Expr) => wp.mkAppNamed (if lc then ``tac_wp_call_lc' else ``tac_wp_call')
    [("Δ", ehyps), ("Δ'", ehyps'), ("e'", wp.wrap e'),
     ("hfv", hfv), ("v2", v2), ("f", f), ("x", x), ("e", body), ("K", wp.quoteK K),
     ("s", wp.s), ("E", wp.E), ("Φ", wp.Φ), ("hlater", hlater),
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
unfolds to a `rec:`/`λ:` value (e.g. a generated `Foo.impl` constant), takes
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
    -- try the `findBindNext` position first, then every position,
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
leading `▷`, and solve trivial `True`/`⌜True⌝`/`emp` goals. -/
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
        -- `True -∗ P`: drop the premise
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

/-- `wp_apply_core lem` applies the specification `lem`
(a Lean lemma or an Iris hypothesis, optionally specialized with
`lem $$ spat1 spat2 ...`) to the WP goal. The conclusion of `lem` must be a WP
(typically `lem` is a Texan triple `{{ P }} e {{ x, RET v; Q }}`); `lem` is
applied to the outermost subexpression `e'` in evaluation position for which
this succeeds, binding the surrounding evaluation context. Premises become new
goals; a leading `▷` on a goal is stripped and trivial `True` goals are closed.
The last goal is the continuation, e.g. `∀ x, Q -∗ WP K[v] {{ Φ }}`.

Unlike `wp_apply` (in `Perennial/Golang/Theory/Auto.lean`), this does no
`isPkgInit` solving, introduction or automation. -/
macro "wp_apply_core " pmt:pmTerm : tactic =>
  `(tactic| focus ((wp_apply_raw $pmt) <;> wp_apply_post); wp_untag_cont)

end Perennial
