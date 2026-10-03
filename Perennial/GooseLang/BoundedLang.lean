/-
The step-bounded GooseLang semantics: the proof device behind time receipts
(Mével, Jourdan, Pottier, "Time credits and time receipts in Iris", ESOP 2019).
Lean addition, no Rocq counterpart.

The real semantics (`base_step`, `goose_real_ectxi_lang` in `Lang.lean`) is the
trusted model of Go and is unchanged. This file adds a separate layer on top of
it: the state of the registered iris-lean language `goose_ectxi_lang` is
`bcfg_state = cfg_state × Nat`, the real configuration together with a counter of
*counted* steps. A base step of the bounded language (`bounded_base_step`) is

* for an uncounted redex: a real base step, counter unchanged;
* for a counted redex, while `counter + 1 < receipt_bound`: a real base step,
  counter incremented (`tick`);
* for a counted redex that is (really) reducible, once
  `receipt_bound ≤ counter + 1`: a *stutter* (expression and state unchanged,
  no observations, no forks).

This is the paper's "`tick` diverges at the limit": the counter never reaches
`receipt_bound`, so `receipt_bound` time receipts are contradictory, while
NotStuck WPs stay provable (a stuttering step is a step). Every bounded step is
backed by a real base step, so bounded reducibility implies real reducibility,
and a real execution of fewer than `receipt_bound` steps is also an execution
of the bounded language (`BoundedLang` simulation lemmas in `Adequacy.lean`).

**Which steps are counted.** The counted redexes are the Go instructions
`App (Val (GoInstruction op)) (Val v)` (function/method resolution, typed
loads/stores/allocations, struct operations, ...). This differs from the
paper, whose tick translation puts a `tick` in front of every operation: a
step that may stutter is neither pure (`PureExec` needs the same reduct in
every state) nor atomic (a stutter does not reach a value), and the program
logic relies on `PureExec` for the pure steps and on `Language.Atomic` for the
heap primitives (`Load`, `AtomicAdd`, `CmpXchg`, ...) around which invariants
and atomic updates are opened. Go instructions are neither: their lifting
lemma (`wp_GoInstruction`) is the only rule for them, so it can absorb the
stutter (by Löb induction) and hand out a receipt. Since every Go function call
and typed memory access goes through a Go instruction, receipts are plentiful;
the adequacy assumption (fewer than `receipt_bound` steps in total) bounds the
number of counted steps a fortiori.
-/
import Perennial.GooseLang.Lang

noncomputable section

namespace Perennial

open Iris.ProgramLogic

/-- The global bound `N` of time receipts: `receipt_bound` receipts are
contradictory, and the adequacy theorems assume executions of fewer than
`receipt_bound` steps. -/
@[irreducible] def receipt_bound : Nat := 2 ^ 48

theorem receipt_bound_eq : receipt_bound = 2 ^ 48 := by
  with_unfolding_all rfl

theorem receipt_bound_pos : 0 < receipt_bound := by
  rw [receipt_bound_eq]; decide

section bounded
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

/-- The state of the bounded language: the real configuration and the number of
counted steps taken so far. -/
abbrev bcfg_state := cfg_state × Nat

/-- The counted redexes: Go instructions. -/
def is_counted : expr → Bool
  | .App (.Val (.GoInstruction _)) (.Val _) => true
  | _ => false

/-- The base step of the bounded language (see the module docstring). -/
inductive bounded_base_step :
    expr → bcfg_state → List observation → expr → bcfg_state → List expr → Prop
  | step {e σ c κ e' σ' efs} :
      is_counted e = false → base_step e σ κ e' σ' efs →
      bounded_base_step e (σ, c) κ e' (σ', c) efs
  | tick {e σ c κ e' σ' efs} :
      is_counted e = true → c + 1 < receipt_bound → base_step e σ κ e' σ' efs →
      bounded_base_step e (σ, c) κ e' (σ', c + 1) efs
  | stutter {e σ c κ e' σ' efs} :
      is_counted e = true → receipt_bound ≤ c + 1 → base_step e σ κ e' σ' efs →
      bounded_base_step e (σ, c) [] e (σ, c) []

theorem bounded_base_step.real {e s κ e' s' efs} (h : bounded_base_step e s κ e' s' efs) :
    ∃ κ' e'' σ'' efs', base_step e s.1 κ' e'' σ'' efs' := by
  cases h with
  | step _ h => exact ⟨_, _, _, _, h⟩
  | tick _ _ h => exact ⟨_, _, _, _, h⟩
  | stutter _ _ h => exact ⟨_, _, _, _, h⟩

/-- For an uncounted redex, bounded and real base steps agree. -/
theorem bounded_base_step_uncounted {e σ c κ e' s' efs} (hnc : is_counted e = false) :
    bounded_base_step e (σ, c) κ e' s' efs ↔ ∃ σ', s' = (σ', c) ∧ base_step e σ κ e' σ' efs := by
  constructor
  · intro h
    cases h with
    | step _ h => exact ⟨_, rfl, h⟩
    | tick h => rw [hnc] at h; cases h
    | stutter h => rw [hnc] at h; cases h
  · rintro ⟨σ', rfl, h⟩
    exact .step hnc h

/-- The registered iris-lean language instance of GooseLang: the bounded layer
over `base_step`. -/
instance goose_ectxi_lang : EctxItemLanguage expr ectx_item bcfg_state observation val where
  toVal := to_val
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl
  baseStep := fun (e, σ) κ (e', σ', efs) => bounded_base_step e σ κ e' σ' efs
  fillItem := fill_item
  fillItem_inj {Ki} := fill_item_inj Ki
  fillItem_val e Ki := fill_item_val Ki e
  fillItem_no_val_inj Ki1 Ki2 := fill_item_no_val_inj Ki1 Ki2
  val_stuck h := by
    obtain ⟨_, _, _, _, h⟩ := bounded_base_step.real h
    exact val_base_stuck h
  base_ctx_step_val {Ki} _ _ _ _ _ _ h := by
    obtain ⟨_, _, _, _, h⟩ := bounded_base_step.real h
    exact base_ctx_step_val Ki h

end bounded

/-! ## The real semantics and the simulation

The real GooseLang language (thread-pool steps, reducibility) is the one that
iris-lean's generic constructions (`EctxItemLanguage → EctxLanguage →
Language`) derive from the trusted `goose_real_ectxi_lang`; it is passed
explicitly since the registered instance is the bounded one. -/

section real
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_semantics ext ffi] [GoGlobalContext]

open Language.Notation EctxLanguage.Notation

/-- The real (unbounded) GooseLang language. -/
abbrev goose_real_lang : Language expr cfg_state observation val :=
  @EctxLanguage.instLanguage _ _ _ _ _
    (@EctxItemLanguage.instEctxLanguage _ _ _ _ _ goose_real_ectxi_lang)

/-- A real primitive (thread) step: a `base_step` in an evaluation context. -/
def real_prim_step (e : expr) (σ : cfg_state) (κ : List observation) (e' : expr)
    (σ' : cfg_state) (efs : List expr) : Prop :=
  @PrimStep.primStep _ _ _ goose_real_lang.toPrimStep (e, σ) κ (e', σ', efs)

/-- `n` steps of the real thread-pool semantics. -/
def real_nsteps (n : Nat) (ρ₁ : List expr × cfg_state) (κs : List observation)
    (ρ₂ : List expr × cfg_state) : Prop :=
  @Language.NSteps _ _ _ _ goose_real_lang n ρ₁ κs ρ₂

/-- A thread is not stuck in the real semantics: it is a value or it can take a
real primitive step. -/
def real_not_stuck (e : expr) (σ : cfg_state) : Prop :=
  (to_val e).isSome ∨ ∃ κ e' σ' efs, real_prim_step e σ κ e' σ' efs

/-- A real thread-pool step from a state whose counter `c` satisfies
`c + 1 < receipt_bound` is also a step of the bounded semantics. -/
theorem bounded_step_of_real {ρ₁ ρ₂ : List expr × cfg_state} {κ : List observation} (c : Nat)
    (h : @Language.Step _ _ _ _ goose_real_lang ρ₁ κ ρ₂) (hc : c + 1 < receipt_bound) :
    ∃ c', c' ≤ c + 1 ∧ Language.Step (ρ₁.1, ((ρ₁.2, c) : bcfg_state)) κ (ρ₂.1, (ρ₂.2, c')) := by
  obtain ⟨H, t₁, t₂⟩ := h
  rename_i e σ e' σ' eₜ
  obtain ⟨hb⟩ := H
  rename_i e₁ e₂ K
  cases hk : is_counted e₁
  · exact ⟨c, by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (bounded_base_step.step (c := c) hk hb)) t₁ t₂⟩
  · exact ⟨c + 1, by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (bounded_base_step.tick hk hc hb)) t₁ t₂⟩

/-- Simulation: a real execution of `n` steps starting with counter `c`, where
`c + n < receipt_bound`, is also an execution of the bounded semantics. -/
theorem bounded_nsteps_of_real {n : Nat} {ρ₁ ρ₂ : List expr × cfg_state} {κs : List observation}
    (h : real_nsteps n ρ₁ κs ρ₂) (c : Nat) (hc : c + n < receipt_bound) :
    ∃ c', Language.NSteps n (ρ₁.1, ((ρ₁.2, c) : bcfg_state)) κs (ρ₂.1, (ρ₂.2, c')) := by
  unfold real_nsteps at h
  induction h generalizing c with
  | refl ρ => exact ⟨c, .refl _⟩
  | cons hstep _ ih =>
    obtain ⟨c₁, hc₁, hstep'⟩ := bounded_step_of_real c hstep (by omega)
    obtain ⟨c', hsteps'⟩ := ih c₁ (by omega)
    exact ⟨c', .cons hstep' hsteps'⟩

/-- Bounded reducibility implies real reducibility: every bounded step is backed
by a real base step. -/
theorem real_not_stuck_of_bounded {e : expr} {σ : cfg_state} {c : Nat}
    (h : PrimStep.NotStuck (e, ((σ, c) : bcfg_state))) : real_not_stuck e σ := by
  rcases h with h | ⟨κ, e', s', efs, H⟩
  · exact .inl h
  · right
    obtain ⟨hb⟩ := H
    rename_i e₁ e₂ K
    obtain ⟨κ', e'', σ'', efs', hr⟩ := bounded_base_step.real hb
    exact ⟨κ', _, σ'', efs', letI := goose_real_ectxi_lang; BaseStep.ContextStep.intro (K := K) hr⟩

end real

end Perennial
