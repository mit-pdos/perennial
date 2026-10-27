/-
Adequacy for a Grove program.

* The program runs against the closed list of extensions `[groveExt]`
  (`groveExts`): the theorem instantiates `goose_adequacy` with it. A program
  proved under `HasExt groveExt` for an arbitrary list instantiates its proof
  with these instances.
* The theorem is fail-stop; Grove has no `ExtCrashInterp`, so no crash adequacy.
* Only the (fail-stop) single-node theorem `grove_single_node_adequacy` is
  proved here. A distributed Grove program is closed off by the distributed
  adequacy theorem `goose_dist_adequacy` (`DistAdequacy.lean`) with these
  instances.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.Ext.Grove.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The extensions of a Grove program: Grove alone. -/
@[reducible] def groveExts : GooseExts := ⟨[groveExt]⟩

attribute [local instance] groveExts

@[reducible] def groveExtsSemantics : GooseSemantics := ⟨(grove_semantics, ⟨⟩)⟩

@[reducible] def groveExtsInterp : GooseInterp := ⟨(grove_interp, ⟨⟩)⟩

attribute [local instance] groveExtsSemantics groveExtsInterp

@[reducible] def groveExts_hasGrove : HasExt groveExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] groveExts_hasGrove

open grove_ext in
/-- Adequacy for a single Grove node (fail-stop). The proof gets ownership of the
initial network and of the node's initial files, and the main thread's token. As
for `goose_adequacy`, the WP is proved for arbitrary time-receipt and thread
bounds `N` and `T` (`receiptBound GF = N`, `threadBound GF = T`) with a
postcondition `φ` that excludes panics (`hφ`), and the conclusion is about real
executions of fewer than `N` steps along which fewer than `T` threads are live:
a final value of the main thread satisfies `φ`, no thread is stuck, and no
thread has an unrecovered panic. -/
theorem grove_single_node_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state) (g : GlobalState)
    (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] e ↦ ms ∈ (extGlobal groveExt g.globalWorld).groveNet, (e c↦ ms : IProp GF)) -∗
        ([∗map] f ↦ c ∈ (extLocal groveExt σ.world).groveNodeFiles, (f f↦ c : IProp GF)) -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_adequacy (GF := GF) N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ ?_ n κs t2 σ2
    Hsteps Hbound Hthreads Hlive
  intro hG HN HT Hlctx
  -- the start resources of `[groveExt]` are Grove's
  have Hg : extsGlobalStart (GF := GF) g.globalWorld ⊢
      [∗map] e ↦ ms ∈ (extGlobal groveExt g.globalWorld).groveNet, (e c↦ ms : IProp GF) :=
    sep_elim_left
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      [∗map] f ↦ c ∈ (extLocal groveExt σ.world).groveNodeFiles, (f f↦ c : IProp GF) :=
    sep_elim_left
  iintro Hnet Hfiles Hgs Htok
  iapply Hwp HN HT Hlctx $$ [Hnet] [Hfiles] Hgs Htok
  · iapply Hg $$ Hnet
  · iapply Hl $$ Hfiles

end Perennial
