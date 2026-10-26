/-
Executions with crashes [Trusted definitions!].

A node has one program, its boot program `boot`: it runs `boot` until it
crashes; the crash kills every thread, and the node restarts with `boot` alone,
from the state that the crash relation `Crash` (`Lang.lean`) gives. There is no
separate recovery procedure. The restarted boot program may crash in turn, any
number of times. `RealCrashNsteps` is such an execution of the real
semantics (the trusted model); the crash adequacy theorem
(`goose_crash_adequacy`, `CrashAdequacy.lean`) is about it.

The rest of the file is the proof device behind that theorem: the same
executions in the bounded semantics (`BoundedLang.lean`), in which a crash
keeps the step fuel (time receipts bound the steps of all generations together)
and resets the thread fuel (thread tokens are per generation), and the
simulation of the real executions by the bounded ones.
-/
module

public import Perennial.GooseLang.BoundedLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris.ProgramLogic

section real
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- An execution with crashes of the real semantics, of `n` steps in all, from
`ρ` to `ρ'`, with boot program `boot`; `b` says whether it crashed. Each
generation takes real steps (`RealNsteps`); a crash, which is not a step,
replaces the thread pool by `[boot]`, the local state `σ` by any `σ'` with
`Crash σ σ'`, and keeps the global state. -/
inductive RealCrashNsteps (boot : Expr) :
    Nat → List Expr × CfgState → List Observation → List Expr × CfgState → Bool → Prop
  | done {n ρ κs ρ'} : RealNsteps n ρ κs ρ' → RealCrashNsteps boot n ρ κs ρ' false
  | crash {n m ρ κs t σ g σ' κs' ρ' b} :
      RealNsteps n ρ κs (t, (σ, g)) → Crash σ σ' →
      RealCrashNsteps boot m ([boot], (σ', g)) κs' ρ' b →
      RealCrashNsteps boot (n + m) ρ (κs ++ κs') ρ' true

/-- The thread bound as a hypothesis on executions with crashes: every
configuration reachable from `ρ` in at most `n` steps, with crashes, has fewer
than `T` live threads. -/
def RealCrashThreadsBelow (boot : Expr) (T n : Nat) (ρ : List Expr × CfgState) : Prop :=
  ∀ k κs ρ' b, k ≤ n → RealCrashNsteps boot k ρ κs ρ' b → ρ'.2.1.threads < T

theorem RealCrashThreadsBelow.start {boot : Expr} {T n : Nat} {ρ : List Expr × CfgState}
    (h : RealCrashThreadsBelow boot T n ρ) : ρ.2.1.threads < T :=
  h 0 [] ρ false (Nat.zero_le _) (.done (@Language.NSteps.refl _ _ _ _ gooseRealLang ρ))

/-! The thread count grows by at most one per step (a `Fork`), and a crash
resets it to one: an execution of `n` steps from a single thread has fewer than
`n + 2` live threads, so the thread bound of the adequacy theorems is no
restriction for it (`RealCrashThreadsBelow.of_single`). -/

theorem real_step_threads {ρ₁ ρ₂ : List Expr × CfgState} {κ : List Observation}
    (h : @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂) :
    ρ₂.2.1.threads ≤ ρ₁.2.1.threads + 1 := by
  obtain ⟨H, t₁, t₂⟩ := h
  obtain ⟨hb⟩ := H
  cases hb with
  | unwind => simp
  | base _ h =>
    cases h with
    | ForkS => simp
    | ThreadExitS => simp; omega
    | ExternalOpS _ _ _ _ _ h => have := extStep_threads h; simp only at this ⊢; omega
    | _ => simp [stateInitHeap, setHeap]

theorem real_nsteps_threads {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps n ρ₁ κs ρ₂) : ρ₂.2.1.threads ≤ ρ₁.2.1.threads + n := by
  unfold RealNsteps at h
  induction h with
  | refl => simp
  | cons hs _ ih => have := real_step_threads hs; omega

theorem real_crash_nsteps_threads {boot : Expr} {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState}
    {κs : List Observation} {b : Bool} (h : RealCrashNsteps boot n ρ₁ κs ρ₂ b) :
    ρ₂.2.1.threads ≤ max ρ₁.2.1.threads 1 + n := by
  induction h with
  | done h => have := real_nsteps_threads h; omega
  | crash h₁ hc _ ih => have := hc.threads; simp only at ih; omega

/-- Every execution with crashes of at most `n` steps from a single thread has
fewer than `n + 2` live threads. -/
theorem RealCrashThreadsBelow.of_single {boot : Expr} {n : Nat} {ρ : List Expr × CfgState}
    (h1 : ρ.2.1.threads = 1) : RealCrashThreadsBelow boot (n + 2) n ρ := by
  intro k κs ρ' b hk h
  have := real_crash_nsteps_threads h
  omega

end real

/-! ## The bounded semantics with crashes, and the simulation -/

section bounded
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- An execution with crashes of the bounded semantics: as `RealCrashNsteps`,
and a crash keeps the step fuel and resets the thread fuel to `T - 2` (the
fuel `goose_init` starts with). -/
inductive BoundedCrashNsteps (boot : Expr) (T : Nat) :
    Nat → List Expr × BcfgState → List Observation → List Expr × BcfgState → Bool → Prop
  | done {n ρ κs ρ'} : Language.NSteps n ρ κs ρ' → BoundedCrashNsteps boot T n ρ κs ρ' false
  | crash {n m ρ κs t σ g f σ' κs' ρ' b} :
      Language.NSteps n ρ κs (t, (((σ, g), f) : BcfgState)) → Crash σ σ' →
      BoundedCrashNsteps boot T m ([boot], (((σ', g), ⟨f.steps, T - 2⟩) : BcfgState)) κs' ρ' b →
      BoundedCrashNsteps boot T (n + m) ρ (κs ++ κs') ρ' true

theorem nsteps_append {n m : Nat} {ρ ρ' ρ'' : List Expr × BcfgState} {κs κs' : List Observation}
    (h : Language.NSteps n ρ κs ρ') (h' : Language.NSteps m ρ' κs' ρ'') :
    Language.NSteps (n + m) ρ (κs ++ κs') ρ'' := by
  induction h with
  | refl => simpa using h'
  | cons hs _ ih => rw [List.append_assoc, Nat.add_right_comm]; exact .cons hs (ih h')

/-- An execution with crashes followed by steps of its last generation. -/
theorem BoundedCrashNsteps.append {boot : Expr} {T n m : Nat} {ρ ρ' ρ'' : List Expr × BcfgState}
    {κs κs' : List Observation} {b : Bool} (h : BoundedCrashNsteps boot T n ρ κs ρ' b)
    (h' : Language.NSteps m ρ' κs' ρ'') : BoundedCrashNsteps boot T (n + m) ρ (κs ++ κs') ρ'' b := by
  induction h with
  | done h => exact .done (nsteps_append h h')
  | crash h₁ hc _ ih => rw [Nat.add_assoc, List.append_assoc]; exact .crash h₁ hc (ih h')

/-- `bounded_nsteps_of_real`, with the step fuel that is left. -/
theorem bounded_nsteps_of_real_fuel {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState}
    {κs : List Observation} (h : RealNsteps n ρ₁ κs ρ₂) (s : Nat) (hs : n ≤ s) (T t : Nat)
    (hT : RealThreadsBelow T n ρ₁) (ht : T - 1 ≤ t + ρ₁.2.1.threads) :
    ∃ s' t', s ≤ s' + n ∧
      Language.NSteps n (ρ₁.1, ((ρ₁.2, ⟨s, t⟩) : BcfgState)) κs (ρ₂.1, (ρ₂.2, ⟨s', t'⟩)) := by
  unfold RealNsteps at h
  induction h generalizing s t with
  | refl ρ => exact ⟨s, t, by omega, .refl _⟩
  | cons hstep hrest ih =>
    rename_i n ρ₁ ρ₂ ρ₃ obs obs'
    have h₂ : ρ₂.2.1.threads < T := (hT.step hstep).start
    obtain ⟨s₁, t₁, hs₁, ht₁, hstep'⟩ := bounded_step_of_real s t T hstep (by omega) ht h₂
    obtain ⟨s', t', hs', hsteps'⟩ := ih s₁ (by omega) t₁ (hT.step hstep) ht₁
    exact ⟨s', t', by omega, .cons hstep' hsteps'⟩

/-- Simulation: a real execution with crashes of `n` steps whose thread count
stays below `T` is also an execution with crashes of the bounded semantics,
started with any step fuel `s ≥ n` and any thread fuel `t ≥ T - 1 - threads`. -/
theorem bounded_crash_nsteps_of_real {boot : Expr} {n : Nat} {ρ ρ' : List Expr × CfgState}
    {κs : List Observation} {b : Bool} (h : RealCrashNsteps boot n ρ κs ρ' b) (s : Nat)
    (hs : n ≤ s) (T t : Nat) (hT : RealCrashThreadsBelow boot T n ρ)
    (ht : T - 1 ≤ t + ρ.2.1.threads) :
    ∃ s' t', BoundedCrashNsteps boot T n (ρ.1, ((ρ.2, ⟨s, t⟩) : BcfgState)) κs
      (ρ'.1, (ρ'.2, ⟨s', t'⟩)) b := by
  induction h generalizing s t with
  | done h =>
    obtain ⟨s', t', -, h'⟩ := bounded_nsteps_of_real_fuel h s hs T t
      (fun k κs ρ' hk hk' => hT k κs ρ' false hk (.done hk')) ht
    exact ⟨s', t', .done h'⟩
  | @crash n m ρ κs t₀ σ g σ' κs' ρ' b h₁ hc _ ih =>
    obtain ⟨s₁, t₁, hs₁, h₁'⟩ := bounded_nsteps_of_real_fuel h₁ s (by omega) T t
      (fun k κs ρ' hk hk' => hT k κs ρ' false (by omega) (.done hk')) ht
    have hT' : RealCrashThreadsBelow boot T m ([boot], (σ', g)) := fun k κs'' ρ'' b' hk hk' =>
      hT (n + k) (κs ++ κs'') ρ'' true (by omega) (.crash h₁ hc hk')
    have h1T : 1 < T := hc.threads ▸ hT'.start
    obtain ⟨s', t', h₂'⟩ := ih s₁ (by omega) (T - 2) hT' (by simp only [hc.threads]; omega)
    exact ⟨s', t', .crash (f := ⟨s₁, t₁⟩) h₁' hc h₂'⟩

end bounded

end Perennial
