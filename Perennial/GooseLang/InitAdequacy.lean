/-
The adequacy theorems, from the trusted initial states.

The adequacy theorems (`goose_adequacy`, `goose_crash_adequacy`,
`goose_dist_adequacy`, `goose_dist_crash_adequacy`, `goose_dist_mixed_crash_adequacy`)
assume that the initial states
satisfy the conditions of the extensions' ghost state (`extsInitgP`, `extsInitP`:
`ExtInterp.initgP`/`initP`), under which they allocate it. Those conditions are part of
the proof, chosen with the interpretation: a theorem stated with them is only as
meaningful as an interpretation nobody audits (one with `initP := False` would make it
vacuous). The versions here are stated with the extensions' initial states of the
trusted semantics instead (`extsInitGlobal`, `extsInitLocal`:
`ExtSemantics.initGlobal`/`initLocal`, `Lang.lean`), which is what a top-level theorem
should assume, and take as a premise that the interpretation accepts them
(`GooseInitCompat`, one `ExtInitCompat` per extension, a proof obligation, not a
trusted assumption). Otherwise their statements are those of the theorems they
specialize.
-/
module

public import Perennial.GooseLang.DistAdequacy

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

section exts
variable [GooseExts] [GooseSemantics] [GooseInterp]

/-- The ghost state of every extension of the program can be allocated for the
initial states of its semantics (`ExtInitCompat`). For a closed list of extensions it
holds by the extensions' instances: `⟨inferInstance, ..., trivial⟩`. -/
abbrev GooseInitCompat : Prop := Exts.InitCompat exts GooseSemantics.sems GooseInterp.interps

theorem extsInitgP_of_init (Hc : GooseInitCompat) {g : GlobalState} (H : extsInitGlobal g) :
    extsInitgP g.globalWorld :=
  Exts.initgP_of_init exts _ _ Hc _ H

theorem extsInitP_of_init (Hc : GooseInitCompat) {σ : state} {g : GlobalState}
    (H : extsInitLocal σ g) : extsInitP σ.world g.globalWorld :=
  Exts.initP_of_init exts _ _ Hc _ _ H

end exts

section adequacy
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- `goose_adequacy`, for a node whose extensions start in an initial state of their
semantics (`extsInitGlobal`, `extsInitLocal`). -/
theorem goose_adequacy_init [hPre : GooseGpreS GF] (Hcompat : GooseInitCompat) (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (HinitG : extsInitGlobal g) (HinitL : extsInitLocal σ g)
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
  goose_adequacy N T e σ g φ hφ (extsInitgP_of_init Hcompat HinitG)
    (extsInitP_of_init Hcompat HinitL) Hwp n κs t2 σ2 Hsteps Hbound Hthreads Hlive

end adequacy

section crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

/-- `goose_crash_adequacy`, for a node whose extensions start in an initial state of
their semantics (`extsInitGlobal`, `extsInitLocal`); after a crash, they are in
whatever state their crash relations give. -/
theorem goose_crash_adequacy_init [hPre : GooseGpreS GF] (Hcompat : GooseInitCompat)
    (N T : Nat) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p))
    (HinitG : extsInitGlobal g) (HinitL : extsInitLocal σ g)
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
      ⊢ P hG.goose_localGS -∗ threadTok -∗ ∀ w, extsLocalCtx w ={⊤}=∗ extsLocalCtx w ∗
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
  goose_crash_adequacy N T e σ g φ hφ (extsInitgP_of_init Hcompat HinitG)
    (extsInitP_of_init Hcompat HinitL) P Hstart Hwp n κs t2 σ2 b Hsteps Hbound Hthreads Hlive

end crash

section dist
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `goose_dist_adequacy`, for a system whose shared state starts in an initial
global state of the extensions' semantics (`extsInitGlobal`) and each of whose nodes
starts in an initial local state (`extsInitLocal`). -/
theorem goose_dist_adequacy_init [hPre : GooseGpreS GF] (Hcompat : GooseInitCompat)
    (N T : Nat) (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (HinitG : extsInitGlobal g)
    (HinitL : ∀ n, n ∈ es → extsInitLocal n.2 g)
    (Hwp : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeWp T n.1 n.2 (φ i))
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistNsteps n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistThreadsBelow T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  goose_dist_adequacy N T es g φ hφ (extsInitgP_of_init Hcompat HinitG)
    (fun n hn => extsInitP_of_init Hcompat (HinitL n hn)) Hwp n κs c Hsteps Hbound Hthreads
    Hlive

end dist

section dist_crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `goose_dist_crash_adequacy`, for a system whose shared state starts in an initial
global state of the extensions' semantics (`extsInitGlobal`) and each of whose nodes
first starts in an initial local state (`extsInitLocal`); a node restarted after a
crash is in whatever state the crash relations give. -/
theorem goose_dist_crash_adequacy_init [hPre : GooseGpreS GF] (Hcompat : GooseInitCompat)
    (N T : Nat) (es : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (HinitG : extsInitGlobal g)
    (HinitL : ∀ n, n ∈ es → extsInitLocal n.2 g)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        [∗list] i ↦ n ∈ es, nodeStart T n.2 (P i))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), es[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok -∗ ∀ w, extsLocalCtx w ={⊤}=∗ extsLocalCtx w ∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (es.map Prod.fst) n (distInit es g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ es → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (es.map Prod.fst) T n (distInit es g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  goose_dist_crash_adequacy N T es g φ hφ (extsInitgP_of_init Hcompat HinitG)
    (fun n hn => extsInitP_of_init Hcompat (HinitL n hn)) P Hstart Hwp n κs c Hsteps Hbound
    Hthreads Hlive


/-- `goose_dist_mixed_crash_adequacy`, for a system whose shared state starts in an
initial global state of the extensions' semantics (`extsInitGlobal`) and each of whose
nodes, crashing or stable, first starts in an initial local state (`extsInitLocal`); a
crashing node restarted after a crash is in whatever state the crash relations give. -/
theorem goose_dist_mixed_crash_adequacy_init [hPre : GooseGpreS GF]
    (Hcompat : GooseInitCompat) (N T : Nat)
    (crashing stable : List (Expr × state)) (g : GlobalState) (φ : Nat → val → Prop)
    (hφ : ∀ i p, ¬ φ i (PanicV p))
    (HinitG : extsInitGlobal g)
    (HinitL : ∀ n, n ∈ crashing ++ stable → extsInitLocal n.2 g)
    (P : ∀ [GooseGlobalGS .hasLC GF], Nat → GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld ={⊤}=∗
        ([∗list] i ↦ n ∈ crashing, nodeStart T n.2 (P i)) ∗
        [∗list] j ↦ n ∈ stable, nodeWp T n.1 n.2 (φ (crashing.length + j)))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      ∀ (i : Nat) (e : Expr) (σ : state), crashing[i]? = some (e, σ) →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P i hG.goose_localGS -∗ threadTok -∗ ∀ w, extsLocalCtx w ={⊤}=∗ extsLocalCtx w ∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ i v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          extsCrashStart hG.goose_localGS L' -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ £ 1 ={⊤}=∗ P i L')
    (n : Nat) (κs : List Observation) (c : DistCfg)
    (Hsteps : DistCrashNsteps (crashing.map Prod.fst) n (distInit (crashing ++ stable) g) κs c)
    (Hbound : n < N) (Hthreads : ∀ n, n ∈ crashing ++ stable → n.2.threads = 1)
    (Hlive : DistCrashThreadsBelow (crashing.map Prod.fst) T n
      (distInit (crashing ++ stable) g)) :
    ∀ i tp σ, c.nodes[i]? = some (tp, σ) →
      (∀ v tp', tp = Val v :: tp' → φ i v) ∧
      (∀ e, e ∈ tp → RealNotStuck e (σ, c.global)) ∧
      (∀ e, e ∈ tp → ¬ UnrecoveredPanic e) :=
  goose_dist_mixed_crash_adequacy N T crashing stable g φ hφ
    (extsInitgP_of_init Hcompat HinitG)
    (fun n hn => extsInitP_of_init Hcompat (HinitL n hn)) P Hstart Hwp n κs c Hsteps Hbound
    Hthreads Hlive

end dist_crash

end Perennial
