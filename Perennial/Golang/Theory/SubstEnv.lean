/-
Parallel substitution of an environment (`substEnv`), used by the WP tactics
(`Perennial/Golang/Theory/ProofMode.lean`) to step through a run of `let:`s of
values at once: the environment is extended by one binding per `let:` (in
constant size), and only the body after the run is traversed, once.

`substEnv σ e` replaces each free variable `y` of `e` with `Val v` when
`σ y = some v` (values are closed, so this is capture-free). Substitution of one
variable is the special case `σ = envIns x v envNil` (`subst_eq_substEnv`), and
substituting into the result of a substitution extends the environment
(`subst_substEnv`).

This is a separate module only for build parallelism (it only needs `Lang`).
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

namespace Perennial

section substEnv
variable [ext : FfiSyntax]

/-- The empty environment. -/
def envNil : String → Option val := fun _ => none

/-- Bind `x` to `v` in `σ`. -/
def envIns (x : String) (v : val) (σ : String → Option val) : String → Option val :=
  fun y => if x = y then some v else σ y

/-- Remove the binder `b` from `σ` (under a `rec:` binding `b`). -/
def envDel (b : Binder) (σ : String → Option val) : String → Option val :=
  match b with
  | BAnon => σ
  | BNamed x => fun y => if x = y then none else σ y

/-- Bind the binder `b` (nothing for `BAnon`), as a `let:` does. -/
def envInsB (b : Binder) (v : val) (σ : String → Option val) : String → Option val :=
  match b with
  | BAnon => σ
  | BNamed x => envIns x v σ

mutual
/-- Substitute the environment `σ` into `e`. -/
def substEnv (σ : String → Option val) : Expr → Expr
  | Val v' => Val v'
  | Var y => match σ y with
    | some v => Val v
    | none => Var y
  | Rec f y e => Rec f y (substEnv (envDel f (envDel y σ)) e)
  | App e1 e2 => App (substEnv σ e1) (substEnv σ e2)
  | If e0 e1 e2 => If (substEnv σ e0) (substEnv σ e1) (substEnv σ e2)
  | Pair e1 e2 => Pair (substEnv σ e1) (substEnv σ e2)
  | Fst e => Fst (substEnv σ e)
  | Snd e => Snd (substEnv σ e)
  | Fork e => Fork (substEnv σ e)
  | Primitive0 op => Primitive0 op
  | Primitive1 op e => Primitive1 op (substEnv σ e)
  | Primitive2 op e1 e2 => Primitive2 op (substEnv σ e1) (substEnv σ e2)
  | ExternalOp op e => ExternalOp op (substEnv σ e)
  | CmpXchg e0 e1 e2 => CmpXchg (substEnv σ e0) (substEnv σ e1) (substEnv σ e2)
  | NewProph => NewProph
  | ResolveProph e1 e2 => ResolveProph (substEnv σ e1) (substEnv σ e2)
  | LiteralValue l => LiteralValue (substEnvKes σ l)
  | SelectStmtClauses d l => SelectStmtClauses (substEnvOpt σ d) (substEnvCcs σ l)
  | Catch e h k => Catch (substEnv σ e) (substEnv σ h) (substEnv σ k)

def substEnvOpt (σ : String → Option val) : Option Expr → Option Expr
  | none => none
  | some e => some (substEnv σ e)

def substEnvKes (σ : String → Option val) : List keyed_element → List keyed_element
  | [] => []
  | ke :: l => substEnvKe σ ke :: substEnvKes σ l

def substEnvKe (σ : String → Option val) : keyed_element → keyed_element
  | KeyedElement k el => KeyedElement (substEnvOkey σ k) (substEnvEl σ el)

def substEnvOkey (σ : String → Option val) : Option key → Option key
  | none => none
  | some (KeyExpression t e) => some (KeyExpression t (substEnv σ e))
  | some (KeyLiteralValue l) => some (KeyLiteralValue (substEnvKes σ l))
  | some k => some k

def substEnvEl (σ : String → Option val) : Element → Element
  | ElementExpression t e => ElementExpression t (substEnv σ e)
  | ElementLiteralValue l => ElementLiteralValue (substEnvKes σ l)

def substEnvCcs (σ : String → Option val) : List comm_clause → List comm_clause
  | [] => []
  | c :: l => substEnvCc σ c :: substEnvCcs σ l

def substEnvCc (σ : String → Option val) : comm_clause → comm_clause
  | CommClause (SendCase t b e) body =>
    CommClause (SendCase t (substEnv σ b) (substEnv σ e)) (substEnv σ body)
  | CommClause (RecvCase t e) body => CommClause (RecvCase t (substEnv σ e)) (substEnv σ body)
end

theorem envDel_apply (b : Binder) (σ : String → Option val) (s : String) :
    envDel b σ s = if BNamed s = b then none else σ s := by
  cases b with
  | BAnon => simp [envDel]
  | BNamed x =>
    by_cases h : x = s
    · subst h; simp [envDel]
    · simp [envDel, h, Ne.symm h]

/-- Substituting `x` into the result of substituting `σ` (without `x`) extends `σ`. -/
theorem envDel_comm_named (x : String) (f y : Binder) (σ : String → Option val)
    (hf : BNamed x ≠ f) (hy : BNamed x ≠ y) :
    envDel f (envDel y (envDel (BNamed x) σ)) = envDel (BNamed x) (envDel f (envDel y σ)) := by
  funext s
  simp only [envDel_apply]
  by_cases h : s = x
  · subst h; simp [hf, hy]
  · simp [h]

theorem envDel_ins_comm (x : String) (v : val) (f y : Binder) (σ : String → Option val)
    (hf : BNamed x ≠ f) (hy : BNamed x ≠ y) :
    envDel f (envDel y (envIns x v σ)) = envIns x v (envDel f (envDel y σ)) := by
  funext s
  simp only [envDel_apply, envIns]
  by_cases h : s = x
  · subst h; simp [hf, hy]
  · simp [Ne.symm h]

theorem envDel_ins_shadow (x : String) (v : val) (f y : Binder) (σ : String → Option val)
    (h : ¬(BNamed x ≠ f ∧ BNamed x ≠ y)) :
    envDel f (envDel y (envDel (BNamed x) σ)) = envDel f (envDel y (envIns x v σ)) := by
  funext s
  simp only [envDel_apply, envIns]
  by_cases hs : s = x
  · subst hs
    have : BNamed s = f ∨ BNamed s = y := by
      by_cases h1 : BNamed s = f
      · exact Or.inl h1
      · exact Or.inr (by simpa [h1] using h)
    rcases this with h1 | h1 <;> simp [h1]
  · simp [hs, Ne.symm hs]

mutual
theorem subst_substEnv (x : String) (v : val) (σ : String → Option val) :
    ∀ e : Expr, subst x v (substEnv (envDel (BNamed x) σ) e) = substEnv (envIns x v σ) e
  | Val _ => by simp only [substEnv, subst]
  | Var y => by
    by_cases h : x = y
    · subst h; simp [substEnv, envDel, envIns, subst]
    · cases hσ : σ y <;> simp [substEnv, envDel, envIns, subst, h, hσ]
  | Rec f y e => by
    simp only [substEnv, subst]
    by_cases hc : BNamed x ≠ f ∧ BNamed x ≠ y
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hc), envDel_comm_named x f y σ hc.1 hc.2, envDel_ins_comm x v f y σ hc.1 hc.2,
        subst_substEnv x v _ e]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hc), envDel_ins_shadow x v f y σ hc]
  | App a b => by simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b]
  | If a b c => by
    simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b, subst_substEnv x v σ c]
  | Pair a b => by simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b]
  | Fst a => by simp only [substEnv, subst, subst_substEnv x v σ a]
  | Snd a => by simp only [substEnv, subst, subst_substEnv x v σ a]
  | Fork a => by simp only [substEnv, subst, subst_substEnv x v σ a]
  | Primitive0 _ => by simp only [substEnv, subst]
  | Primitive1 _ a => by simp only [substEnv, subst, subst_substEnv x v σ a]
  | Primitive2 _ a b => by simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b]
  | ExternalOp _ a => by simp only [substEnv, subst, subst_substEnv x v σ a]
  | CmpXchg a b c => by
    simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b, subst_substEnv x v σ c]
  | NewProph => by simp only [substEnv, subst]
  | ResolveProph a b => by simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b]
  | LiteralValue l => by simp only [substEnv, subst, subst_substEnv_kes x v σ l]
  | SelectStmtClauses d l => by
    simp only [substEnv, subst, subst_substEnv_opt x v σ d, subst_substEnv_ccs x v σ l]
  | Catch a b c => by
    simp only [substEnv, subst, subst_substEnv x v σ a, subst_substEnv x v σ b, subst_substEnv x v σ c]

theorem subst_substEnv_opt (x : String) (v : val) (σ : String → Option val) :
    ∀ d : Option Expr, substOpt x v (substEnvOpt (envDel (BNamed x) σ) d) = substEnvOpt (envIns x v σ) d
  | none => by simp only [substEnvOpt, substOpt]
  | some e => by simp only [substEnvOpt, substOpt, subst_substEnv x v σ e]

theorem subst_substEnv_kes (x : String) (v : val) (σ : String → Option val) :
    ∀ l : List keyed_element,
      substKeyedElements x v (substEnvKes (envDel (BNamed x) σ) l) = substEnvKes (envIns x v σ) l
  | [] => by simp only [substEnvKes, substKeyedElements]
  | ke :: l => by
    simp only [substEnvKes, substKeyedElements, subst_substEnv_ke x v σ ke, subst_substEnv_kes x v σ l]

theorem subst_substEnv_ke (x : String) (v : val) (σ : String → Option val) :
    ∀ ke : keyed_element,
      substKeyedElement x v (substEnvKe (envDel (BNamed x) σ) ke) = substEnvKe (envIns x v σ) ke
  | KeyedElement k el => by
    simp only [substEnvKe, substKeyedElement, subst_substEnv_okey x v σ k, subst_substEnv_el x v σ el]

theorem subst_substEnv_okey (x : String) (v : val) (σ : String → Option val) :
    ∀ k : Option key, substOptKey x v (substEnvOkey (envDel (BNamed x) σ) k) = substEnvOkey (envIns x v σ) k
  | none => by simp only [substEnvOkey, substOptKey]
  | some (KeyField _) => by simp only [substEnvOkey, substOptKey]
  | some (KeyInteger _) => by simp only [substEnvOkey, substOptKey]
  | some (KeyExpression _ e) => by simp only [substEnvOkey, substOptKey, subst_substEnv x v σ e]
  | some (KeyLiteralValue l) => by simp only [substEnvOkey, substOptKey, subst_substEnv_kes x v σ l]

theorem subst_substEnv_el (x : String) (v : val) (σ : String → Option val) :
    ∀ el : Element, substElement x v (substEnvEl (envDel (BNamed x) σ) el) = substEnvEl (envIns x v σ) el
  | ElementExpression _ e => by simp only [substEnvEl, substElement, subst_substEnv x v σ e]
  | ElementLiteralValue l => by simp only [substEnvEl, substElement, subst_substEnv_kes x v σ l]

theorem subst_substEnv_ccs (x : String) (v : val) (σ : String → Option val) :
    ∀ l : List comm_clause,
      substCommClauses x v (substEnvCcs (envDel (BNamed x) σ) l) = substEnvCcs (envIns x v σ) l
  | [] => by simp only [substEnvCcs, substCommClauses]
  | c :: l => by
    simp only [substEnvCcs, substCommClauses, subst_substEnv_cc x v σ c, subst_substEnv_ccs x v σ l]

theorem subst_substEnv_cc (x : String) (v : val) (σ : String → Option val) :
    ∀ c : comm_clause, substCommClause x v (substEnvCc (envDel (BNamed x) σ) c) = substEnvCc (envIns x v σ) c
  | CommClause (SendCase _ b e) body => by
    simp only [substEnvCc, substCommClause, subst_substEnv x v σ b, subst_substEnv x v σ e,
      subst_substEnv x v σ body]
  | CommClause (RecvCase _ e) body => by
    simp only [substEnvCc, substCommClause, subst_substEnv x v σ e, subst_substEnv x v σ body]
end

theorem envDel_nil (b : Binder) : envDel b (envNil : String → Option val) = envNil := by
  funext s; simp [envDel_apply, envNil]

mutual
theorem substEnv_nil : ∀ e : Expr, substEnv envNil e = e
  | Val _ => by simp only [substEnv]
  | Var y => by simp only [substEnv, envNil]
  | Rec f y e => by simp only [substEnv, envDel_nil, substEnv_nil e]
  | App a b => by simp only [substEnv, substEnv_nil a, substEnv_nil b]
  | If a b c => by simp only [substEnv, substEnv_nil a, substEnv_nil b, substEnv_nil c]
  | Pair a b => by simp only [substEnv, substEnv_nil a, substEnv_nil b]
  | Fst a => by simp only [substEnv, substEnv_nil a]
  | Snd a => by simp only [substEnv, substEnv_nil a]
  | Fork a => by simp only [substEnv, substEnv_nil a]
  | Primitive0 _ => by simp only [substEnv]
  | Primitive1 _ a => by simp only [substEnv, substEnv_nil a]
  | Primitive2 _ a b => by simp only [substEnv, substEnv_nil a, substEnv_nil b]
  | ExternalOp _ a => by simp only [substEnv, substEnv_nil a]
  | CmpXchg a b c => by simp only [substEnv, substEnv_nil a, substEnv_nil b, substEnv_nil c]
  | NewProph => by simp only [substEnv]
  | ResolveProph a b => by simp only [substEnv, substEnv_nil a, substEnv_nil b]
  | LiteralValue l => by simp only [substEnv, substEnv_nil_kes l]
  | SelectStmtClauses d l => by simp only [substEnv, substEnv_nil_opt d, substEnv_nil_ccs l]
  | Catch a b c => by simp only [substEnv, substEnv_nil a, substEnv_nil b, substEnv_nil c]

theorem substEnv_nil_opt : ∀ d : Option Expr, substEnvOpt envNil d = d
  | none => by simp only [substEnvOpt]
  | some e => by simp only [substEnvOpt, substEnv_nil e]

theorem substEnv_nil_kes : ∀ l : List keyed_element, substEnvKes envNil l = l
  | [] => by simp only [substEnvKes]
  | ke :: l => by simp only [substEnvKes, substEnv_nil_ke ke, substEnv_nil_kes l]

theorem substEnv_nil_ke : ∀ ke : keyed_element, substEnvKe envNil ke = ke
  | KeyedElement k el => by simp only [substEnvKe, substEnv_nil_okey k, substEnv_nil_el el]

theorem substEnv_nil_okey : ∀ k : Option key, substEnvOkey envNil k = k
  | none => by simp only [substEnvOkey]
  | some (KeyField _) => by simp only [substEnvOkey]
  | some (KeyInteger _) => by simp only [substEnvOkey]
  | some (KeyExpression _ e) => by simp only [substEnvOkey, substEnv_nil e]
  | some (KeyLiteralValue l) => by simp only [substEnvOkey, substEnv_nil_kes l]

theorem substEnv_nil_el : ∀ el : Element, substEnvEl envNil el = el
  | ElementExpression _ e => by simp only [substEnvEl, substEnv_nil e]
  | ElementLiteralValue l => by simp only [substEnvEl, substEnv_nil_kes l]

theorem substEnv_nil_ccs : ∀ l : List comm_clause, substEnvCcs envNil l = l
  | [] => by simp only [substEnvCcs]
  | c :: l => by simp only [substEnvCcs, substEnv_nil_cc c, substEnv_nil_ccs l]

theorem substEnv_nil_cc : ∀ c : comm_clause, substEnvCc envNil c = c
  | CommClause (SendCase _ b e) body => by
    simp only [substEnvCc, substEnv_nil b, substEnv_nil e, substEnv_nil body]
  | CommClause (RecvCase _ e) body => by simp only [substEnvCc, substEnv_nil e, substEnv_nil body]
end

/-- Substitution of one variable is a special case. -/
theorem subst_eq_substEnv (x : String) (v : val) (e : Expr) :
    subst x v e = substEnv (envIns x v envNil) e := by
  have := subst_substEnv x v envNil e
  rwa [envDel_nil, substEnv_nil] at this

/-- A `let:` (or `rec:` with an anonymous name) applied to a value: the reduct of
the beta step under `σ` is the body under `σ` extended with the binding. -/
theorem subst'_substEnv (b : Binder) (v : val) (σ : String → Option val) (e : Expr) :
    subst' b v (subst' BAnon (RecV BAnon b (substEnv (envDel BAnon (envDel b σ)) e))
      (substEnv (envDel BAnon (envDel b σ)) e)) = substEnv (envInsB b v σ) e := by
  cases b with
  | BAnon => rfl
  | BNamed x => exact subst_substEnv x v σ e

/-! ### Equations used to build proofs of `substEnv σ e = e'` -/

theorem substEnv_pf_val (σ : String → Option val) (w : val) : substEnv σ (Val w) = Val w := by
  simp only [substEnv]
theorem substEnv_pf_var_some {σ : String → Option val} {y : String} {w : val} (h : σ y = some w) :
    substEnv σ (Var y) = Val w := by simp only [substEnv, h]
theorem substEnv_pf_var_none {σ : String → Option val} {y : String} (h : σ y = none) :
    substEnv σ (Var y) = Var y := by simp only [substEnv, h]

theorem env_ins_eq (x : String) (v : val) (σ : String → Option val) : envIns x v σ x = some v := by
  simp [envIns]
theorem env_ins_ne {x y : String} {v : val} {σ : String → Option val} {r : Option val}
    (hne : x ≠ y) (h : σ y = r) : envIns x v σ y = r := by simp [envIns, hne, h]
theorem env_del_named_eq (x : String) (σ : String → Option val) : envDel (BNamed x) σ x = none := by
  simp [envDel]
theorem env_del_named_ne {x y : String} {σ : String → Option val} {r : Option val}
    (hne : x ≠ y) (h : σ y = r) : envDel (BNamed x) σ y = r := by simp [envDel, hne, h]
theorem env_del_anon {y : String} {σ : String → Option val} {r : Option val} (h : σ y = r) :
    envDel BAnon σ y = r := h
theorem env_nil (y : String) : (envNil : String → Option val) y = none := rfl
theorem env_insB_eq (x : String) (v : val) (σ : String → Option val) :
    envInsB (BNamed x) v σ x = some v := by simp [envInsB, envIns]
theorem env_insB_ne {x y : String} {v : val} {σ : String → Option val} {r : Option val}
    (hne : x ≠ y) (h : σ y = r) : envInsB (BNamed x) v σ y = r := by simp [envInsB, envIns, hne, h]
theorem env_insB_anon {y : String} {v : val} {σ : String → Option val} {r : Option val}
    (h : σ y = r) : envInsB BAnon v σ y = r := h

section pf
variable {σ : String → Option val}

theorem substEnv_pf_rec {f y : Binder} {e e' : Expr} (h : substEnv (envDel f (envDel y σ)) e = e') :
    substEnv σ (Rec f y e) = Rec f y e' := by simp only [substEnv, h]
theorem substEnv_pf_app {a b a' b' : Expr} (ha : substEnv σ a = a') (hb : substEnv σ b = b') :
    substEnv σ (App a b) = App a' b' := by simp only [substEnv, ha, hb]
theorem substEnv_pf_if {a b c a' b' c' : Expr} (ha : substEnv σ a = a') (hb : substEnv σ b = b')
    (hc : substEnv σ c = c') : substEnv σ (If a b c) = If a' b' c' := by simp only [substEnv, ha, hb, hc]
theorem substEnv_pf_pair {a b a' b' : Expr} (ha : substEnv σ a = a') (hb : substEnv σ b = b') :
    substEnv σ (Pair a b) = Pair a' b' := by simp only [substEnv, ha, hb]
theorem substEnv_pf_fst {a a' : Expr} (ha : substEnv σ a = a') : substEnv σ (Fst a) = Fst a' := by
  simp only [substEnv, ha]
theorem substEnv_pf_snd {a a' : Expr} (ha : substEnv σ a = a') : substEnv σ (Snd a) = Snd a' := by
  simp only [substEnv, ha]
theorem substEnv_pf_fork {a a' : Expr} (ha : substEnv σ a = a') : substEnv σ (Fork a) = Fork a' := by
  simp only [substEnv, ha]
theorem substEnv_pf_prim0 (op : PrimOp0) : substEnv σ (Primitive0 op) = Primitive0 op := by
  simp only [substEnv]
theorem substEnv_pf_prim1 (op : PrimOp1) {a a' : Expr} (ha : substEnv σ a = a') :
    substEnv σ (Primitive1 op a) = Primitive1 op a' := by simp only [substEnv, ha]
theorem substEnv_pf_prim2 (op : PrimOp2) {a b a' b' : Expr} (ha : substEnv σ a = a')
    (hb : substEnv σ b = b') : substEnv σ (Primitive2 op a b) = Primitive2 op a' b' := by
  simp only [substEnv, ha, hb]
theorem substEnv_pf_extop (op : ffi_opcode) {a a' : Expr} (ha : substEnv σ a = a') :
    substEnv σ (ExternalOp op a) = ExternalOp op a' := by simp only [substEnv, ha]
theorem substEnv_pf_cmpxchg {a b c a' b' c' : Expr} (ha : substEnv σ a = a') (hb : substEnv σ b = b')
    (hc : substEnv σ c = c') : substEnv σ (CmpXchg a b c) = CmpXchg a' b' c' := by
  simp only [substEnv, ha, hb, hc]
theorem substEnv_pf_newproph : substEnv σ (NewProph : Expr) = NewProph := by simp only [substEnv]
theorem substEnv_pf_resolve {a b a' b' : Expr} (ha : substEnv σ a = a') (hb : substEnv σ b = b') :
    substEnv σ (ResolveProph a b) = ResolveProph a' b' := by simp only [substEnv, ha, hb]
theorem substEnv_pf_litval {l l' : List keyed_element} (h : substEnvKes σ l = l') :
    substEnv σ (LiteralValue l) = LiteralValue l' := by simp only [substEnv, h]
theorem substEnv_pf_kes_nil : substEnvKes σ [] = [] := by simp only [substEnvKes]
theorem substEnv_pf_kes_cons {ke ke' : keyed_element} {l l' : List keyed_element}
    (h1 : substEnvKe σ ke = ke') (h2 : substEnvKes σ l = l') :
    substEnvKes σ (ke :: l) = ke' :: l' := by simp only [substEnvKes, h1, h2]
theorem substEnv_pf_ke {k k' : Option key} {el el' : Element} (h1 : substEnvOkey σ k = k')
    (h2 : substEnvEl σ el = el') : substEnvKe σ (KeyedElement k el) = KeyedElement k' el' := by
  simp only [substEnvKe, h1, h2]
theorem substEnv_pf_okey_none : substEnvOkey σ none = none := by simp only [substEnvOkey]
theorem substEnv_pf_okey_field (f : GoString) :
    substEnvOkey σ (some (KeyField f)) = some (KeyField f) := by simp only [substEnvOkey]
theorem substEnv_pf_okey_int (i : Int) :
    substEnvOkey σ (some (KeyInteger i)) = some (KeyInteger i) := by simp only [substEnvOkey]
theorem substEnv_pf_okey_expr (t : go.GoType) {e e' : Expr} (h : substEnv σ e = e') :
    substEnvOkey σ (some (KeyExpression t e)) = some (KeyExpression t e') := by
  simp only [substEnvOkey, h]
theorem substEnv_pf_okey_lv {l l' : List keyed_element} (h : substEnvKes σ l = l') :
    substEnvOkey σ (some (KeyLiteralValue l)) = some (KeyLiteralValue l') := by
  simp only [substEnvOkey, h]
theorem substEnv_pf_el_expr (t : go.GoType) {e e' : Expr} (h : substEnv σ e = e') :
    substEnvEl σ (ElementExpression t e) = ElementExpression t e' := by simp only [substEnvEl, h]
theorem substEnv_pf_el_lv {l l' : List keyed_element} (h : substEnvKes σ l = l') :
    substEnvEl σ (ElementLiteralValue l) = ElementLiteralValue l' := by simp only [substEnvEl, h]

end pf

end substEnv

end Perennial
