/-
Distributed adequacy with nodes that crash and nodes that do not (regression test
of `goose_dist_mixed_crash_adequacy`, `DistAdequacy.lean`).

Two nodes run the same program, `checkInit p`: Go's check of whether package `p`
is initialized (the `PackageInitCheck` instruction, which reads the node's
package state). Node 0 starts with no package initialized and may crash; node 1
starts with `p` initialized and never crashes. Node 0 returns `false`: no
package is initialized at its start nor after any of its crashes (a restart
initializes none, `Crash`). Node 1 returns `true`: its proof rests on its start
resource `ownGoState σ₁.goState.packageState`, which a crash would replace by
`ownGoState ∅`.

* `mixed_safety`: the conclusion of `goose_dist_mixed_crash_adequacy` for the
  pair (node 0 crashing, node 1 stable), for every execution in which node 0
  crashes at any time.
* `allCrash_obligation_false`: the theorem is needed. With both nodes crashing,
  `goose_dist_crash_adequacy`'s premises cannot be proved for these programs
  and postconditions (if node 1 can crash at all, which depends on the
  extensions, left abstract here): from any proof of them,
  `goose_dist_crash_adequacy` would apply to the execution in which node 1
  crashes and then returns `false` (`allCrash_execution`).

The extensions are left abstract: the programs use none.
-/
module

public import Perennial.GooseLang.DistAdequacy

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace MixedCrashTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section defs
variable [GooseExts] [GoGlobalContext]

/-- The program of both nodes: is package `p` initialized? -/
def checkInit (p : GoString) : Expr :=
  App (Val (GoInstruction (GoInstruction.PackageInitCheck p))) (Val #())

/-- The postcondition of node `i`: node 1 (stable) returns `true`, node 0
(crashing) returns `false`. -/
def post (i : Nat) (v : val) : Prop := v = #(decide (i = 1))

theorem post_not_panic (i : Nat) (p : val) : ¬ post i (PanicV p) :=
  fun h => intoVal_ne_PanicV _ p h.symm

end defs

/-! ## The program's spec -/

section wp
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem wp_checkInit (p : GoString) (s : GMap GoString Bool) (Φ : val → IProp GF) :
    ⊢ ownGoState s -∗ (ownGoState s -∗ Φ #((s !! p).getD false)) -∗
      WP (checkInit p) @ Stuckness.NotStuck; ⊤ {{ Φ }} := by
  iintro Hown HΦ
  unfold checkInit
  iapply wp_GoInstruction' (s := Stuckness.NotStuck) (E := ⊤) (GoInstruction.PackageInitCheck p)
    #() _ (fun gs => ⟨_, gs, rfl, rfl, rfl⟩)
  inext
  iintro %e' %gs %gs' %Hstep _ Hauth
  obtain ⟨-, rfl, rfl⟩ := Hstep
  icombine Hauth Hown gives %Heq
  subst Heq
  imodintro
  iframe Hauth
  iapply wp_value'
  iapply HΦ $$ Hown

end wp

/-! ## Node 0 crashes, node 1 does not -/

section adequacy
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The crashing nodes: node 0, from `σ₀`. -/
def crashing (p : GoString) (σ₀ : state) : List (Expr × state) := [(checkInit p, σ₀)]

/-- The stable nodes: node 1, from `σ₁`. -/
def stable (p : GoString) (σ₁ : state) : List (Expr × state) := [(checkInit p, σ₁)]

/-- The conclusion of `goose_dist_mixed_crash_adequacy` for the pair, for
executions of fewer than `N` steps along which every node has fewer than `T`
live threads. The precondition of node 0's boot program in a generation `L` is
a fresh package state, which its crash frame gives back after every crash. -/
theorem mixed_safety_bounded [hPre : GooseGpreS GF] (N T : Nat) (p : GoString)
    (σ₀ σ₁ : state) (g : GlobalState)
    (H₀ : σ₀.goState.packageState = ∅) (H₁ : σ₁.goState.packageState !! p = some true)
    (Hthreads₀ : σ₀.threads = 1) (Hthreads₁ : σ₁.threads = 1)
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit₀ : extsInitP σ₀.world g.globalWorld) (Hinit₁ : extsInitP σ₁.world g.globalWorld)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((crashing p σ₀).map Prod.fst) n
      (distInit (crashing p σ₀ ++ stable p σ₁) g) κs c)
    (Hbound : n < N)
    (Hlive : DistCrashThreadsBelow ((crashing p σ₀).map Prod.fst) T n
      (distInit (crashing p σ₀ ++ stable p σ₁) g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → post i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) := by
  have Hmem : ∀ x, x ∈ crashing p σ₀ ++ stable p σ₁ →
      x = (checkInit p, σ₀) ∨ x = (checkInit p, σ₁) := by
    intro x hx
    simpa [crashing, stable] using hx
  refine goose_dist_mixed_crash_adequacy (GF := GF) N T (crashing p σ₀) (stable p σ₁) g post
    post_not_panic Hinitg
    (fun x hx => by rcases Hmem x hx with rfl | rfl <;> assumption)
    (fun _ L => ownGoState (hG := L.goose_go_stateGS) ∅) ?_ ?_ n κs c Hsteps Hbound
    (fun x hx => by rcases Hmem x hx with rfl | rfl <;> assumption) Hlive
  · -- the global setup: node 0's first generation, and node 1's WP
    intro G _
    iintro _
    imodintro
    simp only [crashing, stable, List.length_singleton]
    isplitl []
    · iapply BigSepL.bigSepL_singleton.2
      unfold nodeStart
      iintro %L %_ %_ _ Hgs
      rw [H₀]
      imodintro
      iexact Hgs
    · iapply BigSepL.bigSepL_singleton.2
      unfold nodeWp nodeWpBody
      iintro %L %_ %_ _ Hgs _
      imodintro
      letI : HeapGS .hasLC GF := ⟨G, L⟩
      iapply wp_checkInit p _ _ $$ Hgs
      iintro _
      ipureintro
      simp only [post, H₁, Option.getD_some, Nat.add_zero, decide_true]
  · -- every generation of node 0: it returns `false`, and the next one starts afresh
    intro hG _ _ i e σ Hes _
    obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ e = checkInit p ∧ σ = σ₀ := by
      match i, Hes with
      | 0, Hes => cases Hes; exact ⟨rfl, rfl, rfl⟩
    iintro Hgs _
    imodintro
    isplitl [Hgs]
    · iapply wp_checkInit p _ _ $$ Hgs
      iintro _
      ipureintro
      simp only [post, GMap.lookup_empty, Option.getD_none, Nat.zero_ne_one, decide_false]
    · iintro %L' _ _ Hgs' _
      imodintro
      iexact Hgs'

/-- `mixed_safety_bounded` without bounds: in every execution of the pair in
which node 0 crashes at any time and node 1 never crashes, node 0 returns
`false` and node 1 returns `true` if they return, and no thread is stuck or
has an unrecovered panic. -/
theorem mixed_safety [hPre : GooseGpreS GF] (p : GoString) (σ₀ σ₁ : state) (g : GlobalState)
    (H₀ : σ₀.goState.packageState = ∅) (H₁ : σ₁.goState.packageState !! p = some true)
    (Hthreads₀ : σ₀.threads = 1) (Hthreads₁ : σ₁.threads = 1)
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit₀ : extsInitP σ₀.world g.globalWorld) (Hinit₁ : extsInitP σ₁.world g.globalWorld)
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps ((crashing p σ₀).map Prod.fst) n
      (distInit (crashing p σ₀ ++ stable p σ₁) g) κs c) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → post i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  mixed_safety_bounded (GF := GF) (n + 1) (n + 2) p σ₀ σ₁ g H₀ H₁ Hthreads₀ Hthreads₁ Hinitg
    Hinit₀ Hinit₁ n κs c Hsteps (by omega)
    (DistCrashThreadsBelow.of_single (fun (i : Nat) (tp : List Expr) (σ : state) hi => by
      simp only [distInit, crashing, stable, List.cons_append, List.nil_append, List.map_cons,
        List.map_nil] at hi
      match i, hi with
      | 0, hi => cases hi; exact Hthreads₀
      | 1, hi => cases hi; exact Hthreads₁))

end adequacy

/-! ## With both nodes crashing, the obligation cannot be met -/

section all_crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- From a state with no package initialized, `checkInit p` returns `false`. -/
theorem checkInit_step (p : GoString) (σ : state) (g : GlobalState)
    (Hσ : σ.goState.packageState = ∅) :
    ∃ σ', @Language.Step _ _ _ _ gooseRealLang ([checkInit p], (σ, g)) []
      ([Val #false], (σ', g)) := by
  have Hgo : @IsGoStep _ _ σ.goState.goLctx (GoInstruction.PackageInitCheck p) #() (Val #false)
      σ.goState.packageState σ.goState.packageState := by
    refine ⟨rfl, ?_, rfl⟩
    rw [Hσ]
    rfl
  have Hhead : HeadStep (checkInit p) (σ, g) [] (Val #false)
      ({ σ with goState := { σ.goState with packageState := σ.goState.packageState } }, g) [] :=
    HeadStep.base (by unfold checkInit; not_unwinds)
      (BaseStep.GoInstructionS (GoInstruction.PackageInitCheck p) #() (Val #false)
        σ.goState.packageState (σ, g) Hgo)
  exact ⟨_, @Language.Step.atomic _ _ _ _ gooseRealLang _ _ _ _ _ _
    (letI := gooseRealEctxiLang; BaseStep.ContextStep.intro (K := []) Hhead) [] []⟩

/-- An execution of the pair in which both nodes may crash: node 1 crashes
(into `σ₁'`, which loses its package state), restarts, and returns `false`. -/
theorem allCrash_execution (p : GoString) (σ₀ σ₁ σ₁' : state) (g : GlobalState)
    (Hcrash : Crash σ₁ σ₁') :
    ∃ c σ, DistCrashNsteps ((crashing p σ₀ ++ stable p σ₁).map Prod.fst) 2
        (distInit (crashing p σ₀ ++ stable p σ₁) g) [] c ∧
      c.nodes[1]? = some ([Val #false], σ) := by
  obtain ⟨σ', Hstep⟩ := checkInit_step p σ₁' g Hcrash.packageState
  let nodes₁ : List (List Expr × state) := [([checkInit p], σ₀), ([checkInit p], σ₁')]
  have H1 : DistCrashStep ((crashing p σ₀ ++ stable p σ₁).map Prod.fst)
      (distInit (crashing p σ₀ ++ stable p σ₁) g) [] ⟨nodes₁, g⟩ :=
    DistCrashStep.crash (i := 1) (tp := [checkInit p]) (σ := σ₁) (e := checkInit p) rfl rfl Hcrash
  have H2 : DistCrashStep ((crashing p σ₀ ++ stable p σ₁).map Prod.fst) ⟨nodes₁, g⟩ []
      ⟨nodes₁.set 1 ([Val #false], σ'), g⟩ :=
    DistCrashStep.step (DistStep.node (i := 1) rfl Hstep)
  exact ⟨_, σ', .cons H1 (.cons H2 (.refl _)), rfl⟩

/-- The all-nodes crash obligation cannot be met: for no step bound `N > 2` and
thread bound `T ≥ 4` can the premises of `goose_dist_crash_adequacy` be proved
for the pair with both nodes crashing and the postconditions `post`, whatever
the boot preconditions `P`, as long as node 1 can crash at all (`Hcrash`).
Otherwise `goose_dist_crash_adequacy` would give `post 1 false` for the
execution `allCrash_execution`. -/
theorem allCrash_obligation_false [hPre : GooseGpreS GF] (N T : Nat) (hN : 2 < N) (hT : 4 ≤ T)
    (p : GoString) (σ₀ σ₁ σ₁' : state) (g : GlobalState) (Hcrash : Crash σ₁ σ₁')
    (Hthreads₀ : σ₀.threads = 1) (Hthreads₁ : σ₁.threads = 1)
    (Hinitg : extsInitgP g.globalWorld)
    (Hinit₀ : extsInitP σ₀.world g.globalWorld) (Hinit₁ : extsInitP σ₁.world g.globalWorld)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ crashing p σ₀ ++ stable p σ₁, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), (crashing p σ₀ ++ stable p σ₁)[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜post i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P i L') :
    False := by
  have Hmem : ∀ x, x ∈ crashing p σ₀ ++ stable p σ₁ →
      x = (checkInit p, σ₀) ∨ x = (checkInit p, σ₁) := by
    intro x hx
    simpa [crashing, stable] using hx
  have Hsingle : ∀ (i : Nat) (tp : List Expr) (σ : state),
      (distInit (crashing p σ₀ ++ stable p σ₁) g).nodes[i]? = some (tp, σ) → σ.threads = 1 := by
    intro i tp σ hi
    simp only [distInit, crashing, stable, List.cons_append, List.nil_append, List.map_cons,
      List.map_nil] at hi
    match i, hi with
    | 0, hi => cases hi; exact Hthreads₀
    | 1, hi => cases hi; exact Hthreads₁
  obtain ⟨c, σ, Hsteps, Hc⟩ := allCrash_execution p σ₀ σ₁ σ₁' g Hcrash
  have Hlive : DistCrashThreadsBelow ((crashing p σ₀ ++ stable p σ₁).map Prod.fst) T 2
      (distInit (crashing p σ₀ ++ stable p σ₁) g) :=
    fun k κs c' hk h i tp σ hi =>
      Nat.lt_of_lt_of_le (DistCrashThreadsBelow.of_single Hsingle k κs c' hk h i tp σ hi) hT
  have Hpost := (goose_dist_crash_adequacy (GF := GF) N T (crashing p σ₀ ++ stable p σ₁) g post
    post_not_panic Hinitg (fun x hx => by rcases Hmem x hx with rfl | rfl <;> assumption) P
    Hstart Hwp 2 [] c Hsteps hN
    (fun x hx => by rcases Hmem x hx with rfl | rfl <;> assumption) Hlive 1 _ σ Hc).1 #false [] rfl
  exact absurd (GoGlobalContext.intoVal_inj_bool Hpost) (by decide)

end all_crash

end MixedCrashTest

end Perennial
