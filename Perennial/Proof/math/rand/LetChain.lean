/-
A run of `let:`s of `int64` constants ending in an array literal of the bound variables, as goose
translates a table such as `math/rand`'s `rngCooked` (`var rngCooked [607]int64 = [...]int64{...}`:
`let: "$v0" := c₀ in ... let: "$v606" := c₆₀₆ in [607]int64{"$v0", ..., "$v606"}`), stepped in
one lemma (`wp_letChain_i64Lit`), by induction over the run.

`wp_auto` steps such a run one `let:` at a time; a `let:` whose bound expression is not a value
(a negative constant, `int64(-c)`) ends the run of value `let:`s that it substitutes at once, so it
substitutes into the rest of the run at every such `let:`: quadratic in the length of the table,
which for the 607 entries of `rngCooked` exhausted 40 GB of memory. Here the run is an explicit list
(`letChain`), substituted under an environment (`substEnv`) that grows by one binding per `let:`.
-/
module

public import Perennial.Proof.math.rand.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace math.rand

section defs
variable [GooseExts] [GoGlobalContext]

/-- `let: x₀ := e₀ in ... let: xₙ := eₙ in body`. -/
def letChain : List (String × Expr) → Expr → Expr
  | [], body => body
  | (x, e) :: L, body => Let (BNamed x) e (letChain L body)

/-- An `int64` constant as goose writes it in an array literal: a value, or the negation of an
untyped integer constant converted to `int64`. -/
inductive I64Const : Expr → Prop
  | lit (w : w64) : I64Const (Val #w)
  | negLit (n : Int) : I64Const (App (Val (GoInstruction (Convert go.untypedInt go.int64)))
      (App (Val (GoInstruction (GoUnOp GoNeg go.untypedInt))) (Val #n)))

/-- Every bound expression of the run is an `int64` constant. -/
inductive ChainOk : List (String × Expr) → Prop
  | nil : ChainOk []
  | cons {x : String} {e : Expr} {L : List (String × Expr)} :
      I64Const e → ChainOk L → ChainOk ((x, e) :: L)

/-- The array literal `[n]int64{x₀, ..., xₖ}` of the variables `xs`. -/
def i64Lit (n : Int) (xs : List String) : Expr :=
  App (Val (GoInstruction (CompositeLiteral (go.ArrayType n go.int64))))
    (LiteralValue (xs.map fun x => KeyedElement none (ElementExpression go.int64 (Var x))))

/-- The `let:`s at the head of `e`, as a list (the inverse of `letChain`, `letChain_reify`): lets a
lemma about `letChain L body` apply to the expression of goose's translation, where `L` is
computed by unfolding `reify` instead of being written out. -/
def reify : Expr → List (String × Expr)
  | App (Rec BAnon (BNamed x) b) e => (x, e) :: reify b
  | _ => []

/-- The expression after the `let:`s at the head of `e`. -/
def chainBody : Expr → Expr
  | App (Rec BAnon (BNamed _) b) _ => chainBody b
  | e => e

omit [GoGlobalContext] in
theorem letChain_reify (e : Expr) : letChain (reify e) (chainBody e) = e := by
  fun_induction reify e with
  | case1 x b e ih => simp only [chainBody, letChain, Let, Lam, ih]
  | case2 e h =>
    rw [chainBody.eq_2 e h]
    rfl

/-- The environment of `int64` values `τ`. -/
def envOf (τ : String → Option w64) : String → Option val :=
  fun x => (τ x).map fun w => #w

end defs

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

omit [GooseSemantics] [GooseInterp] in
theorem I64Const.closed {e : Expr} (h : I64Const e) (σ : String → Option val) :
    substEnv σ e = e := by
  cases h <;> simp only [substEnv]

theorem I64Const.wp {e : Expr} (h : I64Const e) :
    ∃ w : w64, ∀ Φ : val → IProp GF, Φ #w ⊢ WP e {{ Φ }} := by
  cases h with
  | lit w => exact ⟨w, fun Φ => by iintro H; wp_pures; iexact H⟩
  | negLit n =>
    refine ⟨W64 (-n), fun Φ => ?_⟩
    iintro H
    wp_pures
    iexact H

omit [GooseSemantics] [GooseInterp] in
theorem substEnvKes_i64Lit (τ : String → Option w64) :
    ∀ xs : List String, (∀ x ∈ xs, (τ x).isSome) →
      substEnvKes (envOf τ) (xs.map fun x => KeyedElement none (ElementExpression go.int64 (Var x))) =
        (xs.map fun x => (τ x).getD (W64 0)).map (arrayLitKE go.int64)
  | [], _ => by simp only [List.map_nil, substEnvKes]
  | x :: xs, h => by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 (h x (List.mem_cons_self ..))
    have ih := substEnvKes_i64Lit τ xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons, substEnvKes, substEnvKe, substEnvOkey, substEnvEl, substEnv, envOf, hw,
      Option.map_some, Option.getD_some, ih, arrayLitKE]

theorem wp_i64Lit (n : Int) (hn : n.toNat < 2 ^ 63) (τ : String → Option w64) (xs : List String)
    (hxs : ∀ x ∈ xs, (τ x).isSome) (hlen : xs.length ≤ n.toNat) (Φ : val → IProp GF) :
    (∀ ws : List w64, ⌜ws.length = xs.length⌝ -∗
      Φ #(array.mk n (ws ++ List.replicate (n.toNat - xs.length) (zero_val w64)))) ⊢
    WP (substEnv (envOf τ) (i64Lit n xs)) {{ Φ }} := by
  iintro H
  simp only [i64Lit, substEnv]
  rw [substEnvKes_i64Lit τ xs hxs]
  wp_pure
  have h := (pure_wp_array_lit n go.int64 (xs.map fun x => (τ x).getD (W64 0))
    (n.toNat - xs.length) _ rfl (by simp only [List.length_map]; omega) hn).pure_wp_wp
      Stuckness.NotStuck ⊤ Φ [] trivial
  dsimp only [fill, List.foldl] at h
  iapply h
  inext
  iintro -
  wp_pures
  iapply H
  ipureintro
  simp only [List.length_map]

omit [GooseSemantics] [GooseInterp] in
theorem envIns_envOf (x : String) (w : w64) (τ : String → Option w64) :
    envIns x #w (envOf τ) = envOf (fun y => if x = y then some w else τ y) := by
  funext y
  simp only [envIns, envOf]
  split <;> simp

theorem wp_letChain (n : Int) (hn : n.toNat < 2 ^ 63) (xs : List String)
    (hlen : xs.length ≤ n.toNat) :
    ∀ (L : List (String × Expr)) (τ : String → Option w64), ChainOk L →
    (∀ x ∈ xs, x ∈ L.map Prod.fst ∨ (τ x).isSome) → ∀ Φ : val → IProp GF,
    (∀ ws : List w64, ⌜ws.length = xs.length⌝ -∗
      Φ #(array.mk n (ws ++ List.replicate (n.toNat - xs.length) (zero_val w64)))) ⊢
    WP (substEnv (envOf τ) (letChain L (i64Lit n xs))) {{ Φ }}
  | [], τ, _, hxs, Φ => by
    refine wp_i64Lit n hn τ xs (fun x hx => ?_) hlen Φ
    rcases hxs x hx with h | h
    · simp at h
    · exact h
  | (x, e) :: L, τ, hok, hxs, Φ => by
    cases hok with
    | cons he hL =>
    obtain ⟨w, hw⟩ := he.wp (GF := GF)
    iintro H
    simp only [letChain, Let, Lam, substEnv, he.closed]
    wp_bind e
    iapply hw
    wp_pure
    wp_pure
    rw [show envDel BAnon (envDel (BNamed x) (envOf τ)) = envDel (BNamed x) (envOf τ) from rfl,
      subst_substEnv, envIns_envOf]
    have hxs' : ∀ y ∈ xs, y ∈ L.map Prod.fst ∨
        ((fun y => if x = y then some w else τ y) y).isSome := by
      intro y hy
      by_cases hxy : x = y
      · right; simp [hxy]
      · rcases hxs y hy with h | h
        · left
          simp only [List.map_cons, List.mem_cons] at h
          exact h.resolve_left (Ne.symm hxy)
        · right; simp [hxy, h]
    iapply wp_letChain n hn xs hlen L _ hL hxs' Φ
    iexact H

/-- **A table of `int64` constants**: the run of `let:`s at the head of `e` binds `int64`
constants and ends in the array literal of its variables (`[n]int64{x₀, ..., xₙ₋₁}`); then `e`
evaluates to some array of `n` elements. The premises are about `reify e` and `chainBody e`, which
the kernel unfolds once along the run (`decide`-free: `ChainOk` by its constructors, the others by
`rfl`). -/
theorem wp_i64Table (n : Int) (hn : n.toNat < 2 ^ 63) (e : Expr) (hL : ChainOk (reify e))
    (hbody : chainBody e = i64Lit n ((reify e).map Prod.fst))
    (hlen : (reify e).length = n.toNat) (Φ : val → IProp GF) :
    (∀ ws : List w64, ⌜ws.length = n.toNat⌝ -∗ Φ #(array.mk n ws)) ⊢ WP e {{ Φ }} := by
  iintro H
  have he := letChain_reify e
  rw [hbody] at he
  rw [← he]
  have h0 : (envOf fun _ => none : String → Option val) = envNil := rfl
  have h := wp_letChain (GF := GF) n hn ((reify e).map Prod.fst) (by simp [hlen]) (reify e)
    (fun _ => none) hL (fun x hx => Or.inl hx) Φ
  rw [h0, substEnv_nil] at h
  iapply h
  iintro %ws %hws
  simp only [List.length_map, hlen, Nat.sub_self, List.replicate_zero, List.append_nil] at hws ⊢
  iapply H
  ipureintro
  exact hws

end wps

end math.rand

end Perennial
