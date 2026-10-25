/-
Distributed GooseLang: the semantics of a system of nodes.

A distributed configuration (`DistCfg`) is a list of nodes, each with its own
thread pool and local state, together with a single global state shared by
all nodes (for the Grove FFI, the network). A distributed step (`DistStep`)
picks a node and takes one thread-pool step of that node's local state paired
with the global state.

Notes:
* There are no crash steps. A fail-stop crash of a node (the node halts for
  good) is subsumed by the scheduler never picking that node again: other
  nodes cannot observe a node's local state, so the global states reachable
  with crashes are reachable without them.
* `DistStep` is generic in the language and in the type of the shared part of
  the state, so that the same definition serves the real semantics
  (`RealDistStep`, over `gooseRealLang`, sharing a `GlobalState`) and the
  step-bounded one (`BDistStep`, over the registered bounded language, sharing
  the `GlobalState` and the fuel). The fuel is shared: the time-receipt bound
  of the adequacy theorems bounds the total number of steps of all nodes.
* The real-to-bounded simulation `bounded_distNsteps_of_real` lifts
  `bounded_step_of_real` node-wise.
-/
module

public import Perennial.GooseLang.BoundedLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris.ProgramLogic Language.Notation

section dist
variable [ext : FfiSyntax] [ffi : FfiModel]

/-- A node of a distributed system: its thread pool and its local state. -/
structure DistNode where
  tpool : List Expr
  localState : state

/-- The initial configuration of a node: one thread running `e` in local state `σ`. -/
abbrev DistNode.init (e : Expr) (σ : state) : DistNode := ⟨[e], σ⟩

end dist

section generic
variable [ext : FfiSyntax] [ffi : FfiModel]
variable {S Gl : Type _} [Λ : Language Expr S Observation val]

/-- One step of a distributed system: node `i` takes a thread-pool step of its
local state paired (by `comb`) with the shared state. -/
inductive DistStep (comb : state → Gl → S) :
    List DistNode × Gl → List Observation → List DistNode × Gl → Prop
  | step {dns : List DistNode} {i : Nat} {t₁ t₂ : List Expr} {σ₁ σ₂ : state} {g₁ g₂ : Gl}
      {κ : List Observation}
      (hi : dns[i]? = some ⟨t₁, σ₁⟩)
      (h : (t₁, comb σ₁ g₁) -<κ>->ₜₚ (t₂, comb σ₂ g₂)) :
      DistStep comb (dns, g₁) κ (dns.set i ⟨t₂, σ₂⟩, g₂)

/-- `n` steps of a distributed system. -/
inductive DistNsteps (comb : state → Gl → S) :
    Nat → List DistNode × Gl → List Observation → List DistNode × Gl → Prop
  | refl (ρ : List DistNode × Gl) : DistNsteps comb 0 ρ [] ρ
  | cons {n : Nat} {ρ₁ ρ₂ ρ₃ : List DistNode × Gl} {κ κs : List Observation} :
      DistStep comb ρ₁ κ ρ₂ → DistNsteps comb n ρ₂ κs ρ₃ →
      DistNsteps comb (n + 1) ρ₁ (κ ++ κs) ρ₃

theorem DistStep.length {comb : state → Gl → S} {ρ₁ ρ₂ : List DistNode × Gl}
    {κ : List Observation} (h : DistStep comb ρ₁ κ ρ₂) : ρ₂.1.length = ρ₁.1.length := by
  cases h; simp

theorem DistNsteps.length {comb : state → Gl → S} {n : Nat} {ρ₁ ρ₂ : List DistNode × Gl}
    {κs : List Observation} (h : DistNsteps comb n ρ₁ κs ρ₂) : ρ₂.1.length = ρ₁.1.length := by
  induction h with
  | refl => rfl
  | cons h _ ih => rw [ih, h.length]

end generic

section real
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- A configuration of a distributed system: the nodes and the global state. -/
abbrev DistCfg := List DistNode × GlobalState

/-- The initial configuration: node `i` runs `ebσs[i].1` in local state
`ebσs[i].2`, and the global state is `g`. -/
def startingDistCfg (ebσs : List (Expr × state)) (g : GlobalState) : DistCfg :=
  (ebσs.map fun ebσ => DistNode.init ebσ.1 ebσ.2, g)

/-- A step of the real (unbounded) distributed semantics. -/
def RealDistStep (ρ₁ : DistCfg) (κ : List Observation) (ρ₂ : DistCfg) : Prop :=
  DistStep (Λ := gooseRealLang) (fun σ g => ((σ, g) : CfgState)) ρ₁ κ ρ₂

/-- `n` steps of the real distributed semantics. -/
def RealDistNsteps (n : Nat) (ρ₁ : DistCfg) (κs : List Observation) (ρ₂ : DistCfg) : Prop :=
  DistNsteps (Λ := gooseRealLang) (fun σ g => ((σ, g) : CfgState)) n ρ₁ κs ρ₂

/-- No thread of a node is stuck (in the real semantics, against global state `g`). -/
def NotStuckNode (dn : DistNode) (g : GlobalState) : Prop :=
  ∀ e, e ∈ dn.tpool → RealNotStuck e (dn.localState, g)

/-- Adequacy of a distributed system started from `startingDistCfg ebσs g`:
in every configuration reachable in fewer than `N` real steps, no thread of
any node is stuck. `N` is the time-receipt bound (see `goose_dist_adequacy`). -/
structure DistAdequate (N : Nat) (ebσs : List (Expr × state)) (g : GlobalState) : Prop where
  not_stuck {n : Nat} {κs : List Observation} {dns : List DistNode} {g' : GlobalState}
    {dn : DistNode} :
    RealDistNsteps n (startingDistCfg ebσs g) κs (dns, g') → n < N →
    dn ∈ dns → NotStuckNode dn g'

end real

section bounded
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiSemantics ext ffi] [GoGlobalContext]

/-- A configuration of the bounded distributed semantics: the nodes, and the
global state with the (shared) fuel. -/
abbrev BDistCfg := List DistNode × (GlobalState × Nat)

/-- How a node's local state and the shared part form the bounded language's state. -/
abbrev bdistComb (σ : state) (gf : GlobalState × Nat) : BcfgState := ((σ, gf.1), gf.2)

/-- A step of the bounded distributed semantics. -/
abbrev BDistStep (ρ₁ : BDistCfg) (κ : List Observation) (ρ₂ : BDistCfg) : Prop :=
  DistStep bdistComb ρ₁ κ ρ₂

/-- `n` steps of the bounded distributed semantics. -/
abbrev BDistNsteps (n : Nat) (ρ₁ : BDistCfg) (κs : List Observation) (ρ₂ : BDistCfg) : Prop :=
  DistNsteps bdistComb n ρ₁ κs ρ₂

/-- A real distributed step from a state with fuel `f > 0` is also a bounded
distributed step, which leaves at least `f - 1` fuel. -/
theorem bounded_distStep_of_real {ρ₁ ρ₂ : DistCfg} {κ : List Observation} (f : Nat)
    (h : RealDistStep ρ₁ κ ρ₂) (hf : 0 < f) :
    ∃ f', f ≤ f' + 1 ∧ BDistStep (ρ₁.1, (ρ₁.2, f)) κ (ρ₂.1, (ρ₂.2, f')) := by
  unfold RealDistStep at h
  cases h with
  | step hi h =>
    obtain ⟨f', hf', h'⟩ := bounded_step_of_real f h hf
    exact ⟨f', hf', .step hi h'⟩

/-- Simulation: a real distributed execution of `n` steps is also an execution
of the bounded distributed semantics started with any fuel `f ≥ n`. -/
theorem bounded_distNsteps_of_real {n : Nat} {ρ₁ ρ₂ : DistCfg} {κs : List Observation}
    (h : RealDistNsteps n ρ₁ κs ρ₂) (f : Nat) (hf : n ≤ f) :
    ∃ f', BDistNsteps n (ρ₁.1, (ρ₁.2, f)) κs (ρ₂.1, (ρ₂.2, f')) := by
  unfold RealDistNsteps at h
  induction h generalizing f with
  | refl ρ => exact ⟨f, .refl _⟩
  | cons hstep _ ih =>
    obtain ⟨f₁, hf₁, hstep'⟩ := bounded_distStep_of_real f hstep (by omega)
    obtain ⟨f', hsteps'⟩ := ih f₁ (by omega)
    exact ⟨f', .cons hstep' hsteps'⟩

end bounded

end Perennial
