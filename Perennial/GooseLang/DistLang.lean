/-
Executions of a distributed system [Trusted definitions!].

A distributed system is a list of nodes (machines) and the state they share.
Each node has its own thread pool and its own local state (`state`: heap, Go
runtime state, the extensions' local states such as a disk, thread count); the
global state (`GlobalState`: the extensions' global states such as a network,
the used prophecy variables) is shared by all nodes. A step of the system is a
step of one node: one thread of that node takes a real step (`gooseRealLang`,
as in a single-node execution) on the node's local state and the global state;
the threads it forks join that node's pool. Nodes interact only through the
global state, that is, through the extensions' operations on it. The nodes
share the encoding of Go values (`GoGlobalContext`), as parts of one Go program
do; each has its own Go context (`goLctx`, the semantics of its Go
instructions).

`DistNsteps` is such an execution of the real semantics (the trusted model);
the distributed adequacy theorem (`goose_dist_adequacy`, `DistAdequacy.lean`)
is about it. It has no crashes.

`DistCrashNsteps boots` adds crashes: a node may crash at any time, which kills
all its threads and restarts it, from the local state that the crash relation
`Crash` (`Lang.lean`) gives, with its *boot program* `boots[i]` alone, the
same program it started with (`distInit`): a node has one program, run at the
start and after every crash, and no separate recovery procedure. A crash
changes neither the other nodes nor the global state (the network). The
distributed crash adequacy theorem (`goose_dist_crash_adequacy`) is about these
executions.

The rest of the file is the proof device behind that theorem: the same
executions in the bounded semantics (`BoundedLang.lean`), in which the step
fuel is global (time receipts bound the steps of all nodes together) and each
node has its own thread fuel (thread tokens are per node), and the simulation
of the real executions by the bounded ones.
-/
module

public import Perennial.GooseLang.CrashLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris.ProgramLogic

section real
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

/-- A configuration of a distributed system: for each node, its thread pool and
its local state; and the global state. -/
structure DistCfg where
  nodes : List (List Expr × state)
  global : GlobalState

/-- A step of a distributed system: the node `i`, with thread pool `tp` and local
state `σ`, takes a real thread-pool step from `(tp, (σ, g))`, which gives it a new
thread pool and local state and gives the system a new global state. -/
inductive DistStep : DistCfg → List Observation → DistCfg → Prop
  | node {nodes : List (List Expr × state)} {g : GlobalState} {i : Nat} {tp : List Expr}
      {σ : state} {κ : List Observation} {tp' : List Expr} {σ' : state} {g' : GlobalState} :
      nodes[i]? = some (tp, σ) →
      @Language.Step _ _ _ _ gooseRealLang (tp, (σ, g)) κ (tp', (σ', g')) →
      DistStep ⟨nodes, g⟩ κ ⟨nodes.set i (tp', σ'), g'⟩

/-- `n` steps of a distributed system, with observations `κs`. -/
inductive DistNsteps : Nat → DistCfg → List Observation → DistCfg → Prop
  | refl (c : DistCfg) : DistNsteps 0 c [] c
  | cons {n : Nat} {c₁ c₂ c₃ : DistCfg} {κ κs : List Observation} :
      DistStep c₁ κ c₂ → DistNsteps n c₂ κs c₃ → DistNsteps (n + 1) c₁ (κ ++ κs) c₃

/-- The initial configuration of a distributed system: node `i` runs the
program `es[i].1` alone (its main thread) from the local state `es[i].2`. -/
def distInit (es : List (Expr × state)) (g : GlobalState) : DistCfg :=
  ⟨es.map (fun n => ([n.1], n.2)), g⟩

/-- The thread bound as a hypothesis on executions of a distributed system:
in every configuration reachable from `c` in at most `n` steps, every node has
fewer than `T` live threads (`state.threads`). -/
def DistThreadsBelow (T n : Nat) (c : DistCfg) : Prop :=
  ∀ k κs c', k ≤ n → DistNsteps k c κs c' →
    ∀ (i : Nat) (tp : List Expr) (σ : state), c'.nodes[i]? = some (tp, σ) → σ.threads < T

/-- A step of a distributed system whose nodes have the boot programs `boots`:
a step of a node, or a crash of a node `i`, which replaces its thread pool by
its boot program `boots[i]` alone and its local state `σ` by any `σ'` with
`Crash σ σ'`, and keeps the other nodes and the global state. -/
inductive DistCrashStep (boots : List Expr) : DistCfg → List Observation → DistCfg → Prop
  | step {c c' : DistCfg} {κ : List Observation} : DistStep c κ c' → DistCrashStep boots c κ c'
  | crash {nodes : List (List Expr × state)} {g : GlobalState} {i : Nat} {tp : List Expr}
      {σ : state} {e : Expr} {σ' : state} :
      nodes[i]? = some (tp, σ) → boots[i]? = some e → Crash σ σ' →
      DistCrashStep boots ⟨nodes, g⟩ [] ⟨nodes.set i ([e], σ'), g⟩

/-- `n` steps (crashes included) of a distributed system with boot programs
`boots`, with observations `κs`. -/
inductive DistCrashNsteps (boots : List Expr) :
    Nat → DistCfg → List Observation → DistCfg → Prop
  | refl (c : DistCfg) : DistCrashNsteps boots 0 c [] c
  | cons {n : Nat} {c₁ c₂ c₃ : DistCfg} {κ κs : List Observation} :
      DistCrashStep boots c₁ κ c₂ → DistCrashNsteps boots n c₂ κs c₃ →
      DistCrashNsteps boots (n + 1) c₁ (κ ++ κs) c₃

/-- `DistThreadsBelow` for executions with crashes: in every configuration
reachable from `c` in at most `n` steps, crashes included, every node has fewer
than `T` live threads. -/
def DistCrashThreadsBelow (boots : List Expr) (T n : Nat) (c : DistCfg) : Prop :=
  ∀ k κs c', k ≤ n → DistCrashNsteps boots k c κs c' →
    ∀ (i : Nat) (tp : List Expr) (σ : state), c'.nodes[i]? = some (tp, σ) → σ.threads < T

end real

/-! ## Facts about the real executions -/

section real_facts
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

theorem DistThreadsBelow.start {T n : Nat} {c : DistCfg} (h : DistThreadsBelow T n c)
    {i : Nat} {tp : List Expr} {σ : state} (hi : c.nodes[i]? = some (tp, σ)) : σ.threads < T :=
  h 0 [] c (Nat.zero_le _) (.refl c) i tp σ hi

theorem DistThreadsBelow.step {T n : Nat} {c c' : DistCfg} {κ : List Observation}
    (h : DistThreadsBelow T (n + 1) c) (hstep : DistStep c κ c') : DistThreadsBelow T n c' := by
  intro k κs c'' hk hsteps
  exact h (k + 1) (κ ++ κs) c'' (by omega) (.cons hstep hsteps)

/-- A step does not change the number of nodes. -/
theorem DistStep.length {c c' : DistCfg} {κ : List Observation} (h : DistStep c κ c') :
    c'.nodes.length = c.nodes.length := by
  cases h; simp

theorem DistNsteps.length {n : Nat} {c c' : DistCfg} {κs : List Observation}
    (h : DistNsteps n c κs c') : c'.nodes.length = c.nodes.length := by
  induction h with
  | refl => rfl
  | cons hs _ ih => rw [ih, hs.length]

/-- The thread count of a node grows by at most one per step. -/
theorem DistStep.threads {c c' : DistCfg} {κ : List Observation} (h : DistStep c κ c')
    {i : Nat} {tp' : List Expr} {σ' : state} (hi : c'.nodes[i]? = some (tp', σ')) :
    ∃ tp σ, c.nodes[i]? = some (tp, σ) ∧ σ'.threads ≤ σ.threads + 1 := by
  cases h with
  | @node nodes g j tp σ κ tp₁ σ₁ g' hj hs =>
    simp only [List.getElem?_set] at hi
    by_cases hij : j = i
    · subst hij
      simp only [show j < nodes.length from (List.getElem?_eq_some_iff.mp hj).1, ite_true] at hi
      cases hi
      exact ⟨tp, σ, hj, real_step_threads hs⟩
    · simp only [hij, ite_false] at hi
      exact ⟨tp', σ', hi, by omega⟩

theorem DistNsteps.threads {n : Nat} {c c' : DistCfg} {κs : List Observation}
    (h : DistNsteps n c κs c') {i : Nat} {tp' : List Expr} {σ' : state}
    (hi : c'.nodes[i]? = some (tp', σ')) :
    ∃ tp σ, c.nodes[i]? = some (tp, σ) ∧ σ'.threads ≤ σ.threads + n := by
  induction h generalizing tp' σ' with
  | refl => exact ⟨tp', σ', hi, by omega⟩
  | cons hs _ ih =>
    obtain ⟨tp₂, σ₂, h₂, hle₂⟩ := ih hi
    obtain ⟨tp₁, σ₁, h₁, hle₁⟩ := hs.threads h₂
    exact ⟨tp₁, σ₁, h₁, by omega⟩

/-- Every execution of at most `n` steps of a distributed system whose nodes
start with a single thread each has fewer than `n + 2` live threads on every
node. -/
theorem DistThreadsBelow.of_single {n : Nat} {c : DistCfg}
    (h1 : ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) → σ.threads = 1) :
    DistThreadsBelow (n + 2) n c := by
  intro k κs c' hk h i tp σ hi
  obtain ⟨tp₀, σ₀, h₀, hle⟩ := h.threads hi
  have := h1 i tp₀ σ₀ h₀
  omega

theorem DistCrashThreadsBelow.start {boots : List Expr} {T n : Nat} {c : DistCfg}
    (h : DistCrashThreadsBelow boots T n c) {i : Nat} {tp : List Expr} {σ : state}
    (hi : c.nodes[i]? = some (tp, σ)) : σ.threads < T :=
  h 0 [] c (Nat.zero_le _) (.refl c) i tp σ hi

theorem DistCrashThreadsBelow.step {boots : List Expr} {T n : Nat} {c c' : DistCfg}
    {κ : List Observation} (h : DistCrashThreadsBelow boots T (n + 1) c)
    (hstep : DistCrashStep boots c κ c') : DistCrashThreadsBelow boots T n c' := by
  intro k κs c'' hk hsteps
  exact h (k + 1) (κ ++ κs) c'' (by omega) (.cons hstep hsteps)

theorem DistCrashStep.length {boots : List Expr} {c c' : DistCfg} {κ : List Observation}
    (h : DistCrashStep boots c κ c') : c'.nodes.length = c.nodes.length := by
  cases h with
  | step h => exact h.length
  | crash => simp

theorem DistCrashNsteps.length {boots : List Expr} {n : Nat} {c c' : DistCfg}
    {κs : List Observation} (h : DistCrashNsteps boots n c κs c') :
    c'.nodes.length = c.nodes.length := by
  induction h with
  | refl => rfl
  | cons hs _ ih => rw [ih, hs.length]

/-- If every node has at most `m ≥ 1` threads, then after `n` steps, crashes
included, every node has at most `m + n` (a crash leaves one). -/
theorem DistCrashNsteps.threads_le {boots : List Expr} {n m : Nat} {c c' : DistCfg}
    {κs : List Observation} (h : DistCrashNsteps boots n c κs c') (hm : 1 ≤ m)
    (hc : ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) → σ.threads ≤ m) :
    ∀ (i : Nat) (tp : List Expr) (σ : state), c'.nodes[i]? = some (tp, σ) → σ.threads ≤ m + n := by
  induction h generalizing m with
  | refl => simpa using hc
  | @cons n c₁ c₂ c₃ κ κs hs _ ih =>
    have h₂ : ∀ (i : Nat) (tp : List Expr) (σ : state), c₂.nodes[i]? = some (tp, σ) →
        σ.threads ≤ m + 1 := by
      intro i tp σ hi
      cases hs with
      | step hs =>
        obtain ⟨tp₀, σ₀, h₀, hle⟩ := hs.threads hi
        have := hc i tp₀ σ₀ h₀
        omega
      | @crash nodes g j tp₁ σ₁ e σ' hj _ hcr =>
        simp only [List.getElem?_set] at hi
        split at hi
        · split at hi
          · cases hi; rw [hcr.threads]; omega
          · cases hi
        · have := hc i tp σ hi; omega
    have := ih (m := m + 1) (by omega) h₂
    intro i tp σ hi
    have := this i tp σ hi
    omega

/-- Every execution with crashes of at most `n` steps of a distributed system
whose nodes start with a single thread each has fewer than `n + 2` live threads
on every node. -/
theorem DistCrashThreadsBelow.of_single {boots : List Expr} {n : Nat} {c : DistCfg}
    (h1 : ∀ (i : Nat) (tp : List Expr) (σ : state), c.nodes[i]? = some (tp, σ) → σ.threads = 1) :
    DistCrashThreadsBelow boots (n + 2) n c := by
  intro k κs c' hk h i tp σ hi
  have := h.threads_le (m := 1) (Nat.le_refl _) (fun i tp σ hi => Nat.le_of_eq (h1 i tp σ hi)) i tp σ hi
  omega

end real_facts

/-! ## The bounded semantics of a distributed system, and the simulation -/

section bounded
variable [GooseExts] [GooseSemantics] [GoGlobalContext]

open Language.Notation

/-- A configuration of a distributed system in the bounded semantics: for each
node its thread pool, its local state and its thread fuel; the global state;
the step fuel, shared by all nodes. -/
structure BDistCfg where
  nodes : List (List Expr × state × Nat)
  global : GlobalState
  steps : Nat

/-- The bounded state of node `i`, with local state `σ` and thread fuel `t`. -/
abbrev BDistCfg.nodeState (c : BDistCfg) (σ : state) (t : Nat) : BcfgState :=
  ((σ, c.global), ⟨c.steps, t⟩)

/-- The configuration after node `i` reaches the thread pool `tp` and the
bounded state `s`. -/
def BDistCfg.setNode (c : BDistCfg) (i : Nat) (tp : List Expr) (s : BcfgState) : BDistCfg :=
  ⟨c.nodes.set i (tp, s.1.1, s.2.threads), s.1.2, s.2.steps⟩

/-- A step of a distributed system in the bounded semantics: a bounded
thread-pool step of one node. -/
def BDistStep (c : BDistCfg) (κ : List Observation) (c' : BDistCfg) : Prop :=
  ∃ i tp σ t tp' s', c.nodes[i]? = some (tp, σ, t) ∧
    Language.Step (tp, c.nodeState σ t) κ (tp', s') ∧ c' = c.setNode i tp' s'

/-- `n` steps of a distributed system in the bounded semantics. -/
inductive BDistNsteps : Nat → BDistCfg → List Observation → BDistCfg → Prop
  | refl (c : BDistCfg) : BDistNsteps 0 c [] c
  | cons {n : Nat} {c₁ c₂ c₃ : BDistCfg} {κ κs : List Observation} :
      BDistStep c₁ κ c₂ → BDistNsteps n c₂ κs c₃ → BDistNsteps (n + 1) c₁ (κ ++ κs) c₃

theorem BDistNsteps.append {n m : Nat} {c₁ c₂ c₃ : BDistCfg} {κs κs' : List Observation}
    (h : BDistNsteps n c₁ κs c₂) (h' : BDistNsteps m c₂ κs' c₃) :
    BDistNsteps (n + m) c₁ (κs ++ κs') c₃ := by
  induction h with
  | refl => simpa using h'
  | cons hs _ ih => rw [List.append_assoc, Nat.add_right_comm]; exact .cons hs (ih h')

theorem BDistCfg.setNode_self {c : BDistCfg} {i : Nat} {tp : List Expr} {σ : state} {t : Nat}
    (hi : c.nodes[i]? = some (tp, σ, t)) : c.setNode i tp (c.nodeState σ t) = c := by
  obtain ⟨nodes, g, s⟩ := c
  simp only [setNode]
  congr
  exact List.set_getElem_self' hi
where
  List.set_getElem_self' {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
      l.set i x = l := by
    obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
    exact List.set_getElem_self hi

theorem BDistCfg.setNode_nodes {c : BDistCfg} {i : Nat} {tp : List Expr} {s : BcfgState} :
    (c.setNode i tp s).nodes[i]? =
      if i < c.nodes.length then some (tp, s.1.1, s.2.threads) else none := by
  simp [setNode, List.getElem?_set]

/-- Thread-pool steps of one node are steps of the system. -/
theorem BDistNsteps.of_node {c : BDistCfg} {i : Nat} (hi : i < c.nodes.length)
    {ρ ρ' : List Expr × BcfgState} (h : ρ -·->ₜₚ* ρ') :
    ∃ n κs, BDistNsteps n (c.setNode i ρ.1 ρ.2) κs (c.setNode i ρ'.1 ρ'.2) := by
  induction h with
  | refl => exact ⟨0, [], .refl _⟩
  | @tail ρ₂ ρ₃ _ hstep ih =>
    obtain ⟨n, κs, hn⟩ := ih
    obtain ⟨κ, hstep⟩ := hstep
    obtain ⟨tp₂, s₂⟩ := ρ₂
    obtain ⟨tp₃, s₃⟩ := ρ₃
    have h1 : BDistStep (c.setNode i tp₂ s₂) κ (c.setNode i tp₃ s₃) := by
      refine ⟨i, tp₂, s₂.1.1, s₂.2.threads, tp₃, s₃, ?_, ?_, ?_⟩
      · simp [BDistCfg.setNode, hi]
      · obtain ⟨⟨σ₂, g₂⟩, ⟨st₂, th₂⟩⟩ := s₂
        exact hstep
      · simp [BDistCfg.setNode]
    have := hn.append (.cons h1 (.refl _))
    exact ⟨n + 1, κs ++ (κ ++ []), by simpa using this⟩

/-- The real configuration of a bounded one. -/
def BDistCfg.erase (c : BDistCfg) : DistCfg :=
  ⟨c.nodes.map (fun n => (n.1, n.2.1)), c.global⟩

/-- The fuel invariant of a bounded configuration for the thread bound `T`:
every node's thread fuel and thread count add up to at least `T - 1`. -/
def BDistCfg.FuelOk (T : Nat) (bc : BDistCfg) : Prop :=
  ∀ (i : Nat) (tp : List Expr) (σ : state) (t : Nat),
    bc.nodes[i]? = some (tp, σ, t) → T - 1 ≤ t + σ.threads

/-- One step of the simulation: a real step of a node, from a configuration
with step fuel left and the fuel invariant, to one where every node has fewer
than `T` threads, is a bounded step that uses at most one step fuel and keeps
the fuel invariant. -/
theorem bdist_step_of_real {c c₂ : DistCfg} {κ : List Observation} (h : DistStep c κ c₂)
    (T : Nat) (bc : BDistCfg) (he : bc.erase = c) (hs : 0 < bc.steps) (ht : bc.FuelOk T)
    (h₂ : ∀ (i : Nat) (tp : List Expr) (σ : state), c₂.nodes[i]? = some (tp, σ) → σ.threads < T) :
    ∃ bc₂, BDistStep bc κ bc₂ ∧ bc₂.erase = c₂ ∧ bc.steps ≤ bc₂.steps + 1 ∧ bc₂.FuelOk T := by
  cases h with
  | @node nodes g i tp σ κ tp' σ' g' hi hs' =>
  obtain ⟨bnodes, bg, bs⟩ := bc
  simp only at hs
  simp only [BDistCfg.erase, DistCfg.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  have hi' := hi
  simp only [List.getElem?_map] at hi'
  obtain ⟨⟨tp₀, σ₀, t⟩, hbi, hx⟩ := Option.map_eq_some_iff.mp hi'
  obtain ⟨rfl, rfl⟩ : tp = tp₀ ∧ σ = σ₀ := by
    simp only [Prod.mk.injEq] at hx; exact ⟨hx.1.symm, hx.2.symm⟩
  have h₂' : σ'.threads < T := by
    refine h₂ i tp' σ' ?_
    simp only [List.getElem?_set, List.length_map,
      (List.getElem?_eq_some_iff.mp hbi).1, ite_true]
  obtain ⟨s₁, t₁, hs₁, ht₁, hb⟩ :=
    bounded_step_of_real (ρ₁ := (tp, (σ, bg))) (ρ₂ := (tp', (σ', g'))) bs t T hs' hs
      (ht i tp σ t hbi) h₂'
  refine ⟨⟨bnodes.set i (tp', σ', t₁), g', s₁⟩, ⟨i, tp, σ, t, tp', ((σ', g'), ⟨s₁, t₁⟩), hbi, hb, rfl⟩,
    by simp [BDistCfg.erase, List.map_set], hs₁, ?_⟩
  intro j tp₂ σ₂ t₂ hj
  simp only [List.getElem?_set] at hj
  split at hj
  · split at hj
    · cases hj; simpa using ht₁
    · exact absurd hj (by simp)
  · exact ht j tp₂ σ₂ t₂ hj

/-- Simulation: a real execution of `n` steps of a distributed system, along
which every node has fewer than `T` threads, is also an execution of the
bounded semantics started with any step fuel `s ≥ n` and any thread fuels
`t ≥ T - 1 - threads`. -/
theorem bdist_nsteps_of_real {n : Nat} {c c' : DistCfg} {κs : List Observation}
    (h : DistNsteps n c κs c') (T : Nat) (hT : DistThreadsBelow T n c) (bc : BDistCfg)
    (he : bc.erase = c) (hs : n ≤ bc.steps) (ht : bc.FuelOk T) :
    ∃ bc', BDistNsteps n bc κs bc' ∧ bc'.erase = c' := by
  induction h generalizing bc with
  | refl => exact ⟨bc, .refl _, he⟩
  | @cons n c₁ c₂ c₃ κ κs hstep hrest ih =>
    have hT' := hT.step hstep
    obtain ⟨bc₂, hb, he₂, hs₂, ht₂⟩ := bdist_step_of_real hstep T bc he (by omega) ht
      (fun i tp σ hi => hT'.start hi)
    obtain ⟨bc', hrest', he'⟩ := ih hT' bc₂ he₂ (by omega) ht₂
    exact ⟨bc', .cons hb hrest', he'⟩

/-! ### Crashes in the bounded semantics -/

/-- A step with crashes of the bounded semantics, for boot programs `boots` and
thread bound `T`: a bounded step of a node, or a crash of a node, which keeps
the step fuel and resets the node's thread fuel to `T - 2` (the fuel of a fresh
node, `bdistInit`). -/
inductive BDistCrashStep (boots : List Expr) (T : Nat) :
    BDistCfg → List Observation → BDistCfg → Prop
  | step {c c' : BDistCfg} {κ : List Observation} : BDistStep c κ c' → BDistCrashStep boots T c κ c'
  | crash {c : BDistCfg} {i : Nat} {tp : List Expr} {σ : state} {t : Nat} {e : Expr}
      {σ' : state} :
      c.nodes[i]? = some (tp, σ, t) → boots[i]? = some e → Crash σ σ' →
      BDistCrashStep boots T c [] ⟨c.nodes.set i ([e], σ', T - 2), c.global, c.steps⟩

inductive BDistCrashNsteps (boots : List Expr) (T : Nat) :
    Nat → BDistCfg → List Observation → BDistCfg → Prop
  | refl (c : BDistCfg) : BDistCrashNsteps boots T 0 c [] c
  | cons {n : Nat} {c₁ c₂ c₃ : BDistCfg} {κ κs : List Observation} :
      BDistCrashStep boots T c₁ κ c₂ → BDistCrashNsteps boots T n c₂ κs c₃ →
      BDistCrashNsteps boots T (n + 1) c₁ (κ ++ κs) c₃

theorem BDistCrashNsteps.append {boots : List Expr} {T n m : Nat} {c₁ c₂ c₃ : BDistCfg}
    {κs κs' : List Observation} (h : BDistCrashNsteps boots T n c₁ κs c₂)
    (h' : BDistCrashNsteps boots T m c₂ κs' c₃) :
    BDistCrashNsteps boots T (n + m) c₁ (κs ++ κs') c₃ := by
  induction h with
  | refl => simpa using h'
  | cons hs _ ih => rw [List.append_assoc, Nat.add_right_comm]; exact .cons hs (ih h')

theorem BDistNsteps.crash {boots : List Expr} {T n : Nat} {c c' : BDistCfg}
    {κs : List Observation} (h : BDistNsteps n c κs c') : BDistCrashNsteps boots T n c κs c' := by
  induction h with
  | refl => exact .refl _
  | cons hs _ ih => exact .cons (.step hs) ih

/-- Simulation with crashes: a real execution with crashes of `n` steps, along
which every node has fewer than `T` threads, is also an execution with crashes
of the bounded semantics started with any step fuel `s ≥ n` and any thread
fuels `t ≥ T - 1 - threads`. -/
theorem bdist_crash_nsteps_of_real {boots : List Expr} {n : Nat} {c c' : DistCfg}
    {κs : List Observation} (h : DistCrashNsteps boots n c κs c') (T : Nat)
    (hT : DistCrashThreadsBelow boots T n c) (bc : BDistCfg)
    (he : bc.erase = c) (hs : n ≤ bc.steps) (ht : bc.FuelOk T) :
    ∃ bc', BDistCrashNsteps boots T n bc κs bc' ∧ bc'.erase = c' := by
  induction h generalizing bc with
  | refl => exact ⟨bc, .refl _, he⟩
  | @cons n c₁ c₂ c₃ κ κs hstep hrest ih =>
    have hT' := hT.step hstep
    cases hstep with
    | step hstep =>
      obtain ⟨bc₂, hb, he₂, hs₂, ht₂⟩ := bdist_step_of_real hstep T bc he (by omega) ht
        (fun i tp σ hi => hT'.start hi)
      obtain ⟨bc', hrest', he'⟩ := ih hT' bc₂ he₂ (by omega) ht₂
      exact ⟨bc', .cons (.step hb) hrest', he'⟩
    | @crash nodes g i tp σ e σ' hi hboot hcr =>
      obtain ⟨bnodes, bg, bs⟩ := bc
      simp only at hs
      simp only [BDistCfg.erase, DistCfg.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hi' := hi
      simp only [List.getElem?_map] at hi'
      obtain ⟨⟨tp₀, σ₀, t⟩, hbi, hx⟩ := Option.map_eq_some_iff.mp hi'
      obtain ⟨rfl, rfl⟩ : tp = tp₀ ∧ σ = σ₀ := by
        simp only [Prod.mk.injEq] at hx; exact ⟨hx.1.symm, hx.2.symm⟩
      have h1T : 1 < T := by
        have := hT'.start (i := i) (tp := [e]) (σ := σ') (by
          simp [(List.getElem?_eq_some_iff.mp hbi).1])
        rw [hcr.threads] at this; exact this
      obtain ⟨bc', hrest', he'⟩ := ih hT' ⟨bnodes.set i ([e], σ', T - 2), bg, bs⟩
        (by simp [BDistCfg.erase, List.map_set]) (by simp only; omega)
        (by
          intro j tp₂ σ₂ t₂ hj
          simp only [List.getElem?_set] at hj
          split at hj
          · split at hj
            · cases hj; rw [hcr.threads]; omega
            · cases hj
          · exact ht j tp₂ σ₂ t₂ hj)
      exact ⟨bc', .cons (.crash hbi hboot hcr) hrest', he'⟩

end bounded

end Perennial
