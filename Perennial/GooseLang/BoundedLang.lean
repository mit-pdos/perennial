/-
The bounded GooseLang semantics: the proof device behind time receipts (Mével,
Jourdan, Pottier, "Time credits and time receipts in Iris", ESOP 2019) and
thread tokens (`Threads.lean`).

The real semantics (`HeadStep`, `gooseRealEctxiLang` in `Lang.lean`) is the
trusted model of Go and is unchanged. This file adds a separate layer on top of
it: the state of the registered iris-lean language `goose_ectxi_lang` is
`BcfgState = CfgState × Fuel`, the real configuration together with a *fuel*
`⟨s, t⟩`: `s` counted steps and `t` thread forks may still be taken. A base
step of the bounded language (`BoundedBaseStep`) is, by the kind of the redex
(`redexKind`):

* for a plain redex: a real base step, fuel unchanged;
* for a counted redex (a Go instruction), with step fuel `s + 1`: a real base
  step, step fuel `s` (`tick`); with step fuel `0` and (really) reducible: a
  *stutter* (expression and state unchanged, no observations, no forks);
* for `Fork e`, with thread fuel `t + 1`: the real fork (it spawns
  `e ;; ThreadExit` and increments `GlobalState.threads`), thread fuel `t`;
  with thread fuel `0`: a stutter (`forkStutter`);
* for `ThreadExit` (the last step of a forked thread), with thread fuel `t`:
  the real step (it decrements `GlobalState.threads`), thread fuel `t + 1`.

**Time receipts.** The bound `N` of time receipts is not a parameter of the
language: it is the initial step fuel plus one. The adequacy theorems
(`Adequacy.lean`) start the bounded semantics with step fuel `N - 1` for an
arbitrary `N > 0` chosen by the client, and the receipt ghost state
(`receiptGS`, `Receipts.lean`) records `N` as `receiptBound`; the state
interpretation ties the two together (step fuel `s` means `N - 1 - s` counted
steps so far, `receiptFuel`). This is the paper's "`tick` diverges at the
limit": at most `N - 1` counted steps succeed, so `N` time receipts are
contradictory, while NotStuck WPs stay provable (a stuttering step is a step).

**Thread tokens.** Likewise the bound `T` on live threads is the initial thread
fuel plus two: the adequacy theorems start with thread fuel `T - 2` for an
arbitrary `T > 1` (the main thread is live), and the thread ghost state
(`ThreadGS`, `Threads.lean`) records `T` as `threadBound`. The state
interpretation owns the thread fuel as `t` thread tokens (`threadFuel t`); a
`Fork` takes one out and the forking thread receives it (`wp_fork_tok`), a
`ThreadExit` puts one back (`wp_ThreadExit`). Together with the main thread's
token, at most `T - 1` tokens exist, so `T` thread tokens are contradictory
(`threadBound_elim`): a counter that is backed by one token per live thread,
such as a `WaitGroup`'s, is below `T`. Along a real execution whose thread
count `GlobalState.threads` stays below `T` (the hypothesis `RealThreadsBelow`
of `goose_adequacy`), the thread fuel is at least `T - 1 - threads`
(`bounded_step_of_real`), so every real `Fork` is a bounded `fork`, not a
stutter.

Every bounded step is backed by a real base step, so bounded reducibility
implies real reducibility, and a real execution of at most `s` steps whose
thread count stays below `T` is also an execution of the bounded language
started with fuel `⟨s, T - 1 - threads⟩` (simulation lemmas below).

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
stutter (by Löb induction) and hand out a receipt; the same holds of `Fork`
(`wp_fork_tok`). Since every Go function call and typed memory access goes
through a Go instruction, receipts are plentiful; the adequacy assumption
(fewer than `N` steps in total) bounds the number of counted steps a fortiori.
-/
module

public import Perennial.GooseLang.Lang

@[expose] public section

noncomputable section

namespace Perennial

open Iris.ProgramLogic

section bounded
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- The fuel of the bounded language: `steps`, the number of counted steps that
may still be taken (time receipts), and `threads`, the number of threads that
may still be forked (thread tokens). -/
structure Fuel where
  steps : Nat
  threads : Nat
deriving Inhabited

/-- The state of the bounded language: the real configuration and the fuel. -/
abbrev BcfgState := CfgState × Fuel

/-- How the bounded semantics treats a redex. -/
inductive RedexKind where
  /-- a Go instruction: a counted step (time receipts) -/
  | counted
  /-- `Fork`: consumes thread fuel -/
  | fork
  /-- `ThreadExit`: returns thread fuel -/
  | exit
  /-- anything else: a real step with the fuel unchanged -/
  | plain
deriving DecidableEq

def redexKind : Expr → RedexKind
  -- a Go instruction applied to a panic unwinds (`Unwinds`): a plain step
  | .App (.Val (.GoInstruction _)) (.Val (.PanicV _)) => .plain
  | .App (.Val (.GoInstruction _)) (.Val _) => .counted
  | .Fork _ => .fork
  | .Primitive0 .ThreadExitOp => .exit
  | _ => .plain

theorem redexKind_GoInstruction {op : GoInstruction} {v : val} (hv : v.isPanic = false) :
    redexKind (.App (.Val (.GoInstruction op)) (.Val v)) = .counted := by
  cases v <;> simp_all [redexKind, val.isPanic]

theorem redexKind_eq_fork {e : Expr} (h : redexKind e = .fork) : ∃ e', e = Fork e' := by
  unfold redexKind at h
  split at h <;> simp_all

theorem redexKind_eq_exit {e : Expr} (h : redexKind e = .exit) : e = ThreadExit := by
  unfold redexKind at h
  split at h <;> simp_all

/-- The base step of the bounded language (see the module docstring). -/
inductive BoundedBaseStep :
    Expr → BcfgState → List Observation → Expr → BcfgState → List Expr → Prop
  | step {e σ f κ e' σ' efs} :
      redexKind e = .plain → HeadStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, f) κ e' (σ', f) efs
  | tick {e σ s t κ e' σ' efs} :
      redexKind e = .counted → HeadStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, ⟨s + 1, t⟩) κ e' (σ', ⟨s, t⟩) efs
  | stutter {e σ t κ e' σ' efs} :
      redexKind e = .counted → HeadStep e σ κ e' σ' efs →
      BoundedBaseStep e (σ, ⟨0, t⟩) [] e (σ, ⟨0, t⟩) []
  | fork {e σ s t κ e' σ' efs} :
      HeadStep (Fork e) σ κ e' σ' efs →
      BoundedBaseStep (Fork e) (σ, ⟨s, t + 1⟩) κ e' (σ', ⟨s, t⟩) efs
  | forkStutter {e σ s} :
      BoundedBaseStep (Fork e) (σ, ⟨s, 0⟩) [] (Fork e) (σ, ⟨s, 0⟩) []
  | exit {σ s t κ e' σ' efs} :
      HeadStep ThreadExit σ κ e' σ' efs →
      BoundedBaseStep ThreadExit (σ, ⟨s, t⟩) κ e' (σ', ⟨s, t + 1⟩) efs

theorem not_unwinds_Fork (e : Expr) : ∀ p, ¬ Unwinds (Fork e) p := by not_unwinds

theorem not_unwinds_ThreadExit : ∀ p, ¬ Unwinds ThreadExit p := by not_unwinds

theorem not_unwinds_GoInstruction {op : GoInstruction} {v : val} (hv : v.isPanic = false) :
    ∀ p, ¬ Unwinds (App (Val (GoInstruction op)) (Val v)) p := by not_unwinds

theorem BoundedBaseStep.real {e s κ e' s' efs} (h : BoundedBaseStep e s κ e' s' efs) :
    ∃ κ' e'' σ'' efs', HeadStep e s.1 κ' e'' σ'' efs' := by
  cases h with
  | step _ h => exact ⟨_, _, _, _, h⟩
  | tick _ h => exact ⟨_, _, _, _, h⟩
  | stutter _ h => exact ⟨_, _, _, _, h⟩
  | fork h => exact ⟨_, _, _, _, h⟩
  | forkStutter => exact ⟨_, _, _, _, .base (not_unwinds_Fork _) (BaseStep.ForkS _ _)⟩
  | exit h => exact ⟨_, _, _, _, h⟩

/-- For a plain redex, bounded and real base steps agree. -/
theorem boundedBaseStep_plain {e σ f κ e' s' efs} (hp : redexKind e = .plain) :
    BoundedBaseStep e (σ, f) κ e' s' efs ↔ ∃ σ', s' = (σ', f) ∧ HeadStep e σ κ e' σ' efs := by
  constructor
  · intro h
    cases h with
    | step _ h => exact ⟨_, rfl, h⟩
    | tick h => rw [hp] at h; cases h
    | stutter h => rw [hp] at h; cases h
    | fork h => simp [redexKind] at hp
    | forkStutter => simp [redexKind] at hp
    | exit h => simp [redexKind] at hp
  · rintro ⟨σ', rfl, h⟩
    exact .step hp h

/-- The registered iris-lean language instance of GooseLang: the bounded layer
over `base_step`. -/
instance goose_ectxi_lang : EctxItemLanguage Expr EctxItem BcfgState Observation val where
  toVal := toVal
  ofVal := Val
  coe_of_toVal_eq_some := of_to_val
  toVal_coe _ := rfl
  baseStep := fun (e, σ) κ (e', σ', efs) => BoundedBaseStep e σ κ e' σ' efs
  fillItem := fillItem
  fillItem_inj {Ki} := fillItem_inj Ki
  fillItem_val e Ki := fillItem_val Ki e
  fillItem_no_val_inj Ki1 Ki2 := fillItem_no_val_inj Ki1 Ki2
  val_stuck h := by
    obtain ⟨_, _, _, _, h⟩ := BoundedBaseStep.real h
    exact val_head_stuck h
  base_ctx_step_val {Ki} _ _ _ _ _ _ h := by
    obtain ⟨_, _, _, _, h⟩ := BoundedBaseStep.real h
    exact head_ctx_step_val Ki h

end bounded

/-! ## The real semantics and the simulation

The real GooseLang language (thread-pool steps, reducibility) is the one that
iris-lean's generic constructions (`EctxItemLanguage → EctxLanguage →
Language`) derive from the trusted `gooseRealEctxiLang`; it is passed
explicitly since the registered instance is the bounded one. -/

section real
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

open Language.Notation EctxLanguage.Notation

/-- The real (unbounded) GooseLang language. -/
abbrev gooseRealLang : Language Expr CfgState Observation val :=
  @EctxLanguage.instLanguage _ _ _ _ _
    (@EctxItemLanguage.instEctxLanguage _ _ _ _ _ gooseRealEctxiLang)

/-- A real primitive (thread) step: a `base_step` in an evaluation context. -/
def RealPrimStep (e : Expr) (σ : CfgState) (κ : List Observation) (e' : Expr)
    (σ' : CfgState) (efs : List Expr) : Prop :=
  @PrimStep.primStep _ _ _ gooseRealLang.toPrimStep (e, σ) κ (e', σ', efs)

/-- `n` steps of the real thread-pool semantics. -/
def RealNsteps (n : Nat) (ρ₁ : List Expr × CfgState) (κs : List Observation)
    (ρ₂ : List Expr × CfgState) : Prop :=
  @Language.NSteps _ _ _ _ gooseRealLang n ρ₁ κs ρ₂

/-- A thread is not stuck in the real semantics: it is a value or it can take a
real primitive step. -/
def RealNotStuck (e : Expr) (σ : CfgState) : Prop :=
  (toVal e).isSome ∨ ∃ κ e' σ' efs, RealPrimStep e σ κ e' σ' efs

/-- The thread bound as a hypothesis on real executions: every configuration
reachable from `ρ` in at most `n` real steps has fewer than `T` live threads
(`GlobalState.threads`: the main thread and the forked threads that have not
reached their `ThreadExit`). -/
def RealThreadsBelow (T n : Nat) (ρ : List Expr × CfgState) : Prop :=
  ∀ k κs ρ', k ≤ n → RealNsteps k ρ κs ρ' → ρ'.2.2.threads < T

theorem RealThreadsBelow.start {T n : Nat} {ρ : List Expr × CfgState}
    (h : RealThreadsBelow T n ρ) : ρ.2.2.threads < T :=
  h 0 [] ρ (Nat.zero_le _) (@Language.NSteps.refl _ _ _ _ gooseRealLang ρ)

theorem RealThreadsBelow.step {T n : Nat} {ρ ρ' : List Expr × CfgState} {κ : List Observation}
    (h : RealThreadsBelow T (n + 1) ρ) (hstep : @Language.Step _ _ _ _ gooseRealLang ρ κ ρ') :
    RealThreadsBelow T n ρ' := by
  intro k κs ρ'' hk hsteps
  exact h (k + 1) (κ ++ κs) ρ'' (by omega)
    (@Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hstep hsteps)

/-- A head step that is neither a fork nor an exit does not change the thread count. -/
theorem baseStep_threads {e : Expr} {σ : CfgState} {κ : List Observation} {e' : Expr}
    {σ' : CfgState} {efs : List Expr} (h : HeadStep e σ κ e' σ' efs)
    (hf : redexKind e ≠ .fork) (hx : redexKind e ≠ .exit) : σ'.2.threads = σ.2.threads := by
  cases h with
  | unwind => rfl
  | base _ h =>
    cases h with
    | ForkS => exact absurd rfl hf
    | ThreadExitS => exact absurd rfl hx
    | ExternalOpS _ _ _ _ _ h => exact ffi_step_threads h
    | _ => rfl

/-- A real thread-pool step from a state with step fuel `s > 0` and thread fuel
`t` with `T - 1 ≤ t + threads`, to a configuration with fewer than `T` threads,
is also a step of the bounded semantics, which leaves at least `s - 1` step
fuel and thread fuel `t'` with `T - 1 ≤ t' + threads'`. -/
theorem bounded_step_of_real {ρ₁ ρ₂ : List Expr × CfgState} {κ : List Observation}
    (s t T : Nat) (h : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) (hs : 0 < s)
    (ht : T - 1 ≤ t + ρ₁.2.2.threads) (h₂ : ρ₂.2.2.threads < T) :
    ∃ s' t', s ≤ s' + 1 ∧ T - 1 ≤ t' + ρ₂.2.2.threads ∧
      Language.Step (ρ₁.1, ((ρ₁.2, ⟨s, t⟩) : BcfgState)) κ (ρ₂.1, (ρ₂.2, ⟨s', t'⟩)) := by
  obtain ⟨H, t₁, t₂⟩ := h
  rename_i e σ e' σ' eₜ
  obtain ⟨hb⟩ := H
  rename_i e₁ e₂ K
  simp only at ht h₂ ⊢
  rcases hk : redexKind e₁ with _ | _ | _ | _
  · -- counted
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have hth := baseStep_threads hb (by simp [hk]) (by simp [hk])
    exact ⟨s', t, by omega, by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.tick hk hb)) t₁ t₂⟩
  · -- fork
    obtain ⟨e₀, rfl⟩ := redexKind_eq_fork hk
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_Fork _ _)
    cases hb
    simp only at h₂
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact ⟨s, t', by omega, by simp; omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.fork
        (.base (not_unwinds_Fork _) (BaseStep.ForkS e₀ σ)))) t₁ t₂⟩
  · -- exit
    have := redexKind_eq_exit hk
    subst this
    rcases hb with ⟨hu⟩ | ⟨_, hb⟩
    · exact absurd hu (not_unwinds_ThreadExit _)
    cases hb
    exact ⟨s, t + 1, by omega, by simp; omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.exit
        (.base not_unwinds_ThreadExit (BaseStep.ThreadExitS σ)))) t₁ t₂⟩
  · -- plain
    have hth := baseStep_threads hb (by simp [hk]) (by simp [hk])
    exact ⟨s, t, by omega, by omega, Language.Step.atomic
      (BaseStep.ContextStep.intro (K := K) (BoundedBaseStep.step hk hb)) t₁ t₂⟩

/-- Simulation: a real execution of `n` steps whose thread count stays below `T`
is also an execution of the bounded semantics started with any step fuel
`s ≥ n` and any thread fuel `t ≥ T - 1 - threads`. -/
theorem bounded_nsteps_of_real {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps n ρ₁ κs ρ₂) (s : Nat) (hs : n ≤ s) (T t : Nat)
    (hT : RealThreadsBelow T n ρ₁) (ht : T - 1 ≤ t + ρ₁.2.2.threads) :
    ∃ s' t', Language.NSteps n (ρ₁.1, ((ρ₁.2, ⟨s, t⟩) : BcfgState)) κs (ρ₂.1, (ρ₂.2, ⟨s', t'⟩)) := by
  unfold RealNsteps at h
  induction h generalizing s t with
  | refl ρ => exact ⟨s, t, .refl _⟩
  | cons hstep hrest ih =>
    rename_i n ρ₁ ρ₂ ρ₃ obs obs'
    have h₂ : ρ₂.2.2.threads < T := (hT.step hstep).start
    obtain ⟨s₁, t₁, hs₁, ht₁, hstep'⟩ := bounded_step_of_real s t T hstep (by omega) ht h₂
    obtain ⟨s', t', hsteps'⟩ := ih s₁ (by omega) t₁ (hT.step hstep) ht₁
    exact ⟨s', t', .cons hstep' hsteps'⟩

/-- Bounded reducibility implies real reducibility: every bounded step is backed
by a real base step. -/
theorem realNotStuck_of_bounded {e : Expr} {σ : CfgState} {f : Fuel}
    (h : PrimStep.NotStuck (e, ((σ, f) : BcfgState))) : RealNotStuck e σ := by
  rcases h with h | ⟨κ, e', s', efs, H⟩
  · exact .inl h
  · right
    obtain ⟨hb⟩ := H
    rename_i e₁ e₂ K
    obtain ⟨κ', e'', σ'', efs', hr⟩ := BoundedBaseStep.real hb
    exact ⟨κ', _, σ'', efs', letI := gooseRealEctxiLang; BaseStep.ContextStep.intro (K := K) hr⟩

end real

end Perennial
