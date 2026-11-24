/-
Adequacy with the thread bound as a property of the execution itself.

`goose_adequacy` (`Adequacy.lean`) takes the thread bound as `RealThreadsBelow T n ρ`: *every*
execution of at most `n` steps from `ρ` keeps fewer than `T` threads live. That premise is about
the program, not about the execution the theorem concludes about, and for a program whose
goroutine count an adversarial schedule can grow without limit (a ticker goroutine that fires
forever while the goroutines it spawns are never scheduled) it is false for large `n`. A client
whose proof needs a constant thread bound `T` (a `WaitGroup` counter backed by thread tokens) can
then only discharge it from the step count, `T = n + 2` (`real_nsteps_threads`), which caps
the theorem at `T - 2` steps.

The proof of `goose_adequacy` uses the premise only along the given execution
(`bounded_nsteps_of_real` applies it to each configuration of that execution). This file states
that directly: `RealNstepsBelow T n ρ κs ρ'` is an execution of `n` real steps every configuration
of which (the first and the last included) has fewer than `T` live threads, and
`goose_adequacy_below` concludes about every such execution of fewer than `N` steps. The executions
it excludes are exactly those in which `T` goroutines are live at once.

`RealNstepsBelow.of_threadsBelow` recovers `goose_adequacy`'s premises from the new one, so
`goose_adequacy` follows from `goose_adequacy_below` (`goose_adequacy_of_below`, a check).

The same for executions with crashes: `RealCrashNstepsBelow boot T n ρ κs ρ' b` is an execution
with crashes (`RealCrashNsteps`) each generation of which is a `RealNstepsBelow T`, and
`goose_crash_adequacy_below` is `goose_crash_adequacy` about every such execution
(`goose_crash_adequacy_of_below`, the check). The distributed forms over `DistCrashNstepsBelow`
are in `DistAdequacy.lean`.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.CrashLang
public import Perennial.GooseLang.CrashAdequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

section real
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- `n` steps of the real thread-pool semantics along which every configuration, the first and
the last included, has fewer than `T` live threads (`state.threads`: the main thread and the
forked threads that have not reached their `ThreadExit`). -/
inductive RealNstepsBelow (T : Nat) :
    Nat → List Expr × CfgState → List Observation → List Expr × CfgState → Prop
  | refl (ρ : List Expr × CfgState) : ρ.2.1.threads < T → RealNstepsBelow T 0 ρ [] ρ
  | cons {n : Nat} {ρ₁ ρ₂ ρ₃ : List Expr × CfgState} {κ κs : List Observation} :
      ρ₁.2.1.threads < T →
      @Language.Step _ _ _ _ gooseRealLang ρ₁ κ ρ₂ →
      RealNstepsBelow T n ρ₂ κs ρ₃ →
      RealNstepsBelow T (n + 1) ρ₁ (κ ++ κs) ρ₃

namespace RealNstepsBelow

/-- The execution, forgetting the thread bound. -/
theorem nsteps {T n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNstepsBelow T n ρ₁ κs ρ₂) : RealNsteps n ρ₁ κs ρ₂ := by
  induction h with
  | refl ρ _ => exact @Language.NSteps.refl _ _ _ _ gooseRealLang ρ
  | cons _ hstep _ ih => exact @Language.NSteps.cons _ _ _ _ gooseRealLang _ _ _ _ _ _ hstep ih

/-- The first configuration has fewer than `T` threads. -/
theorem start {T n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNstepsBelow T n ρ₁ κs ρ₂) : ρ₁.2.1.threads < T := by
  cases h with
  | refl _ h => exact h
  | cons h _ _ => exact h

/-- `goose_adequacy`'s premises give the new one: if every execution of at most `n` steps from
`ρ₁` stays below `T` threads, so does this one. -/
theorem of_threadsBelow {T n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps n ρ₁ κs ρ₂) (hT : RealThreadsBelow T n ρ₁) :
    RealNstepsBelow T n ρ₁ κs ρ₂ := by
  unfold RealNsteps at h
  induction h with
  | refl ρ => exact .refl ρ hT.start
  | cons hstep _ ih => exact .cons hT.start hstep (ih (hT.step hstep))

/-- A bound on all executions of `n` steps from one thread: each step forks at most one
thread, so `n + 2` bounds every execution of `n` steps from a configuration with one thread. -/
theorem of_one {n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNsteps n ρ₁ κs ρ₂) (h1 : ρ₁.2.1.threads = 1) :
    RealNstepsBelow (n + 2) n ρ₁ κs ρ₂ :=
  of_threadsBelow h fun _ _ _ hk hs => by have := real_nsteps_threads hs; omega

/-- A larger bound. -/
theorem mono {T T' n : Nat} {ρ₁ ρ₂ : List Expr × CfgState} {κs : List Observation}
    (h : RealNstepsBelow T n ρ₁ κs ρ₂) (hTT : T ≤ T') : RealNstepsBelow T' n ρ₁ κs ρ₂ := by
  induction h with
  | refl ρ h => exact .refl ρ (by omega)
  | cons h hstep _ ih => exact .cons (by omega) hstep ih

end RealNstepsBelow

/-- Simulation: a real execution of `n` steps every configuration of which has fewer than `T`
threads is also an execution of the bounded semantics started with any step fuel `s ≥ n` and
any thread fuel `t ≥ T - 1 - threads` (`bounded_nsteps_of_real`, with the thread bound read off
the execution). -/
theorem bounded_nsteps_of_real_below {T n : Nat} {ρ₁ ρ₂ : List Expr × CfgState}
    {κs : List Observation} (h : RealNstepsBelow T n ρ₁ κs ρ₂) (s : Nat) (hs : n ≤ s) (t : Nat)
    (ht : T - 1 ≤ t + ρ₁.2.1.threads) :
    ∃ s' t', Language.NSteps n (ρ₁.1, ((ρ₁.2, ⟨s, t⟩) : BcfgState)) κs (ρ₂.1, (ρ₂.2, ⟨s', t'⟩)) := by
  induction h generalizing s t with
  | refl ρ _ => exact ⟨s, t, .refl _⟩
  | cons _ hstep hrest ih =>
    obtain ⟨s₁, t₁, hs₁, ht₁, hstep'⟩ :=
      bounded_step_of_real s t T hstep (by omega) ht hrest.start
    obtain ⟨s', t', hsteps'⟩ := ih s₁ (by omega) t₁ ht₁
    exact ⟨s', t', .cons hstep' hsteps'⟩

end real

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- **Adequacy of GooseLang, with the thread bound on the execution.** As `goose_adequacy`, but
about every real execution of `e` of fewer than `N` steps, from a configuration with the main
thread only, *along which* fewer than `T` threads are live at every configuration
(`RealNstepsBelow T n`): the main thread's result satisfies `φ`, every thread is a value or can
take a step, and no thread has an unrecovered panic. -/
theorem goose_adequacy_below [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hsteps.start; simp only at this; omega
  have Hadeq := goose_adequacy_blang N T (by omega) hT e σ g φ Hinitg Hinit Hwp
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real_below Hsteps (N - 1) (by omega) (T - 2)
    (by simp only; omega)
  have Hreach : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* (t2, (σ2, ⟨c, t⟩)) :=
    (Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro v t2' rfl
    exact Hadeq.adequate_result t2' (σ2, ⟨c, t⟩) v Hreach
  · intro e2 he2
    exact realNotStuck_of_bounded (Hadeq.adequate_not_stuck t2 (σ2, ⟨c, t⟩) e2 rfl Hreach he2)
  · exact goose_no_unrecovered_panic_blang N T (by omega) hT e σ g φ hφ Hinitg Hinit Hwp Hb

/-- Check: `goose_adequacy` is the instance of `goose_adequacy_below` at an execution all of
whose executions of `n` steps stay below `T` threads (`RealNstepsBelow.of_threadsBelow`). -/
theorem goose_adequacy_of_below [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  goose_adequacy_below N T e σ g φ hφ Hinitg Hinit Hwp n κs t2 σ2
    (RealNstepsBelow.of_threadsBelow Hsteps Hlive) Hbound Hthreads

/-- Invariance (real semantics), with the thread bound on the execution: as `goose_invariance`,
for every configuration reached by a real execution of fewer than `N` steps along which fewer
than `T` threads are live. -/
theorem goose_invariance_below [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φinv : ExtsGlobalState exts → Prop)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', extsGlobalCtx (GF := GF) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : CfgState}
    (Hsteps : RealNstepsBelow T n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    φinv σ2.2.globalWorld := by
  have hT : 1 < T := by have := Hsteps.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real_below Hsteps (N - 1) (by omega) (T - 2)
    (by simp only; omega)
  exact goose_invariance_blang (σ2 := (σ2, ⟨c, t⟩)) N T (by omega) hT e σ g φinv Hinitg Hinit Hwp
    ((Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩)


end adequacy

/-! ## Executions with crashes -/

section real_crash
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- An execution with crashes of the real semantics (`RealCrashNsteps`) along which every
configuration, the first and the last of each generation included, has fewer than `T` live
threads: each generation is a `RealNstepsBelow T`. A crash (not a step) replaces the thread
pool by `[boot]`, the local state `σ` by any `σ'` with `Crash σ σ'`, and keeps the global state;
the restarted configuration is the first of the next generation, so it is bounded too. -/
inductive RealCrashNstepsBelow (boot : Expr) (T : Nat) :
    Nat → List Expr × CfgState → List Observation → List Expr × CfgState → Bool → Prop
  | done {n ρ κs ρ'} : RealNstepsBelow T n ρ κs ρ' → RealCrashNstepsBelow boot T n ρ κs ρ' false
  | crash {n m ρ κs t σ g σ' κs' ρ' b} :
      RealNstepsBelow T n ρ κs (t, (σ, g)) → Crash σ σ' →
      RealCrashNstepsBelow boot T m ([boot], (σ', g)) κs' ρ' b →
      RealCrashNstepsBelow boot T (n + m) ρ (κs ++ κs') ρ' true

namespace RealCrashNstepsBelow

/-- The execution, forgetting the thread bound. -/
theorem nsteps {boot : Expr} {T n : Nat} {ρ ρ' : List Expr × CfgState} {κs : List Observation}
    {b : Bool} (h : RealCrashNstepsBelow boot T n ρ κs ρ' b) : RealCrashNsteps boot n ρ κs ρ' b := by
  induction h with
  | done h => exact .done h.nsteps
  | crash h hc _ ih => exact .crash h.nsteps hc ih

/-- The first configuration has fewer than `T` threads. -/
theorem start {boot : Expr} {T n : Nat} {ρ ρ' : List Expr × CfgState} {κs : List Observation}
    {b : Bool} (h : RealCrashNstepsBelow boot T n ρ κs ρ' b) : ρ.2.1.threads < T := by
  cases h with
  | done h => exact h.start
  | crash h _ _ => exact h.start

/-- `goose_crash_adequacy`'s premises give the new one: if every execution with crashes of at
most `n` steps from `ρ` stays below `T` threads, so does this one. -/
theorem of_threadsBelow {boot : Expr} {T n : Nat} {ρ ρ' : List Expr × CfgState}
    {κs : List Observation} {b : Bool} (h : RealCrashNsteps boot n ρ κs ρ' b)
    (hT : RealCrashThreadsBelow boot T n ρ) : RealCrashNstepsBelow boot T n ρ κs ρ' b := by
  induction h with
  | done h =>
    exact .done (RealNstepsBelow.of_threadsBelow h
      (fun k κs ρ' hk hk' => hT k κs ρ' false hk (.done hk')))
  | @crash n m ρ κs t σ g σ' κs' ρ' b h₁ hc _ ih =>
    exact .crash (RealNstepsBelow.of_threadsBelow h₁
        (fun k κs₀ ρ₀ hk hk' => hT k κs₀ ρ₀ false (by omega) (.done hk'))) hc
      (ih fun k κs'' ρ'' b' hk hk' => hT (n + k) (κs ++ κs'') ρ'' true (by omega) (.crash h₁ hc hk'))

/-- From a configuration with one thread, an execution with crashes of `n` steps stays below
`n + 2` threads (a step forks at most one thread, a crash leaves one). -/
theorem of_single {boot : Expr} {n : Nat} {ρ ρ' : List Expr × CfgState} {κs : List Observation}
    {b : Bool} (h : RealCrashNsteps boot n ρ κs ρ' b) (h1 : ρ.2.1.threads = 1) :
    RealCrashNstepsBelow boot (n + 2) n ρ κs ρ' b :=
  of_threadsBelow h (RealCrashThreadsBelow.of_single h1)

/-- A larger bound. -/
theorem mono {boot : Expr} {T T' n : Nat} {ρ ρ' : List Expr × CfgState} {κs : List Observation}
    {b : Bool} (h : RealCrashNstepsBelow boot T n ρ κs ρ' b) (hTT : T ≤ T') :
    RealCrashNstepsBelow boot T' n ρ κs ρ' b := by
  induction h with
  | done h => exact .done (h.mono hTT)
  | crash h hc _ ih => exact .crash (h.mono hTT) hc ih

end RealCrashNstepsBelow

/-- `bounded_nsteps_of_real_below`, with the step fuel that is left. -/
theorem bounded_nsteps_of_real_below_fuel {T n : Nat} {ρ₁ ρ₂ : List Expr × CfgState}
    {κs : List Observation} (h : RealNstepsBelow T n ρ₁ κs ρ₂) (s : Nat) (hs : n ≤ s) (t : Nat)
    (ht : T - 1 ≤ t + ρ₁.2.1.threads) :
    ∃ s' t', s ≤ s' + n ∧
      Language.NSteps n (ρ₁.1, ((ρ₁.2, ⟨s, t⟩) : BcfgState)) κs (ρ₂.1, (ρ₂.2, ⟨s', t'⟩)) := by
  induction h generalizing s t with
  | refl ρ _ => exact ⟨s, t, by omega, .refl _⟩
  | cons _ hstep hrest ih =>
    obtain ⟨s₁, t₁, hs₁, ht₁, hstep'⟩ :=
      bounded_step_of_real s t T hstep (by omega) ht hrest.start
    obtain ⟨s', t', hs', hsteps'⟩ := ih s₁ (by omega) t₁ ht₁
    exact ⟨s', t', by omega, .cons hstep' hsteps'⟩

/-- Simulation with crashes, with the thread bound along the execution: a real execution with
crashes of `n` steps every configuration of which has fewer than `T` threads is also an execution
with crashes of the bounded semantics, started with any step fuel `s ≥ n` and any thread fuel
`t ≥ T - 1 - threads` (`bounded_crash_nsteps_of_real`, with the thread bound read off the
execution). -/
theorem bounded_crash_nsteps_of_real_below {boot : Expr} {T n : Nat} {ρ ρ' : List Expr × CfgState}
    {κs : List Observation} {b : Bool} (h : RealCrashNstepsBelow boot T n ρ κs ρ' b) (s : Nat)
    (hs : n ≤ s) (t : Nat) (ht : T - 1 ≤ t + ρ.2.1.threads) :
    ∃ s' t', BoundedCrashNsteps boot T n (ρ.1, ((ρ.2, ⟨s, t⟩) : BcfgState)) κs
      (ρ'.1, (ρ'.2, ⟨s', t'⟩)) b := by
  induction h generalizing s t with
  | done h =>
    obtain ⟨s', t', -, h'⟩ := bounded_nsteps_of_real_below_fuel h s hs t ht
    exact ⟨s', t', .done h'⟩
  | @crash n m ρ κs t₀ σ g σ' κs' ρ' b h₁ hc hrest ih =>
    obtain ⟨s₁, t₁, hs₁, h₁'⟩ := bounded_nsteps_of_real_below_fuel h₁ s (by omega) t ht
    have h1T : 1 < T := hc.threads ▸ hrest.start
    obtain ⟨s', t', h₂'⟩ := ih s₁ (by omega) (T - 2) (by simp only [hc.threads]; omega)
    exact ⟨s', t', .crash (f := ⟨s₁, t₁⟩) h₁' hc h₂'⟩

end real_crash

section crash_adequacy
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

/-- **Crash adequacy of GooseLang, with the thread bound on the execution.** As
`goose_crash_adequacy`, but about every real execution with crashes of the boot program `e` of
fewer than `N` steps in all, from a configuration with the main thread only, *along which* fewer
than `T` threads are live at every configuration (`RealCrashNstepsBelow e T n`): if the main
thread has terminated with `v` then `φ v`, every thread is a value or can take a step, and no
thread has an unrecovered panic. -/
theorem goose_crash_adequacy_below [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNstepsBelow e T n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hsteps.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_crash_nsteps_of_real_below Hsteps (N - 1) (by omega) (T - 2)
    (by simp only; omega)
  have H := goose_crash_adequacy_blang N T (by omega) hT e σ g φ hφ Hinitg Hinit P Hstart Hwp Hb
  refine ⟨H.1, fun e2 he2 => realNotStuck_of_bounded (H.2.1 e2 he2), ?_⟩
  intro e2 He2 Hu
  obtain ⟨p, Hp⟩ := unrecoveredPanic_steps Hu
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem He2
  obtain ⟨m, κs', Hm⟩ := (Language.erasedStep_nSteps _ _).mp (Hp [] t₁ t₂ (σ2, ⟨c, t⟩))
  have := (goose_crash_adequacy_blang N T (by omega) hT e σ g φ hφ Hinitg Hinit P Hstart Hwp
    (Hb.append Hm)).2.2 (PanicV p) (by simp)
  simp [val.isPanic] at this

/-- Check: `goose_crash_adequacy` is the instance of `goose_crash_adequacy_below` at an execution
all of whose executions with crashes of `n` steps stay below `T` threads
(`RealCrashNstepsBelow.of_threadsBelow`). -/
theorem goose_crash_adequacy_of_below [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  goose_crash_adequacy_below N T e σ g φ hφ Hinitg Hinit P Hstart Hwp n κs t2 σ2 b
    (RealCrashNstepsBelow.of_threadsBelow Hsteps Hlive) Hbound Hthreads

end crash_adequacy

end Perennial
