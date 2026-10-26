/-
Crash adequacy for a program with a filesystem.

* The filesystem survives a crash with its ghost state: the files are
  unchanged (`fs_semantics`), so the new generation keeps the old generation's
  file ghost state (`crashStart old new := ⌜new = old⌝`), and the old
  generation's `f fs↦ c` describe the files after the crash.
* The program runs against the closed list of extensions `[fsExt]` (`fsExts`):
  `fs_crash_adequacy` instantiates `goose_crash_adequacy` with it, handing the
  program the ownership of the initial files.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import Perennial.GooseLang.Ext.Fs.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-- The filesystem keeps its ghost state across a crash. -/
instance fs_crash_interp : ExtCrashInterp fsExt where
  crashStart hL hL' := iprop(⌜hL' = hL⌝)
  local_crash _ _ hL σ σ' h := by
    obtain rfl := (show σ' = σ from h)
    iintro H
    imodintro
    iexists hL
    iframe H
    ipureintro; rfl

/-- The extensions of a filesystem program: the filesystem alone. -/
@[reducible] def fsExts : GooseExts := ⟨[fsExt]⟩

attribute [local instance] fsExts

@[reducible] def fsExtsSemantics : GooseSemantics := ⟨(fs_semantics, ⟨⟩)⟩

@[reducible] def fsExtsInterp : GooseInterp := ⟨(fs_interp, ⟨⟩)⟩

attribute [local instance] fsExtsSemantics fsExtsInterp

@[reducible] def fsExtsCrashInterp : GooseCrashInterp := ⟨(fs_crash_interp, ⟨⟩)⟩

attribute [local instance] fsExtsCrashInterp

@[reducible] def fsExts_hasFs : HasExt fsExt where
  mem := .here
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] fsExts_hasFs

/-- Ghost state for a filesystem program: one slot for each camera that
`GooseGpreS` needs for `[fsExt]`, so that a client's adequacy theorem need not
assume any. -/
noncomputable def fsGF : BundledGFunctors := fun
  | 0 => ⟨AllURF, inferInstance⟩
  | 1 => ⟨InvMapF, inferInstance⟩
  | 2 => ⟨constOF CoPsetDisjL, inferInstance⟩
  | 3 => ⟨constOF (DisjointLeibnizSet PosSet), inferInstance⟩
  | 4 => ⟨Auth.AuthURF (constOF Credit), inferInstance⟩
  | 5 => ⟨constOF (NaHeapUR Loc val), inferInstance⟩
  | 6 => ⟨constOF (HeapView proph_id (Agree (DiscreteO (List val))) (GMap proph_id)), inferInstance⟩
  | 7 => ⟨constOF (HeapView GoString (Agree (DiscreteO (List w8))) (GMap GoString)), inferInstance⟩
  | 8 => ⟨constOF (HeapView GoString (Agree (DiscreteO GName)) (GMap GoString)), inferInstance⟩
  | 9 => ⟨constOF MetaUR, inferInstance⟩
  | 10 => ⟨GhostVarF (GMap GoString Bool), inferInstance⟩
  | _ => ⟨constOF Unit, inferInstance⟩

noncomputable instance fsGpreS : GooseGpreS fsGF where
  goose_preG_iris := ⟨⟨⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩⟩, ⟨⟨4, rfl⟩⟩⟩
  goose_preG_heap := ⟨⟨5, rfl⟩⟩
  goose_preG_proph := ⟨⟨⟨6, rfl⟩⟩⟩
  goosePreGExts := (⟨⟨⟨7, rfl⟩⟩, ⟨⟨8, rfl⟩⟩, ⟨9, rfl⟩⟩, PUnit.unit)
  goose_preG_go_state := ⟨@GhostVarG.mk _ _ ⟨10, rfl⟩⟩
  goosePreGAllG := allGOfSlot 0 rfl

open fs_ext in
/-- Crash adequacy for a filesystem boot program `e` (`goose_crash_adequacy`
for `[fsExt]`): the precondition `P` holds of the first generation, from the
ownership of the initial files, and every generation proves the WP of `e` from
`P` and guarantees `P` of the next generation `L'` after it crashes, from its
`crashed` and from the files' ghost state of `L'` being its own (so that its
`f fs↦ c` describe the files after the crash). -/
theorem fs_crash_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state) (g : GlobalState)
    (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (P : ∀ [GooseGlobalGS .hasLC GF], GooseLocalGS GF → IProp GF)
    (Hstart : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF)) -∗
        ownGoState σ.goState.packageState ={⊤}=∗ P hG.goose_localGS)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ P hG.goose_localGS -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗
        ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
          ⌜extLocalGS fsExt (L := L') = extLocalGS fsExt (L := hG.goose_localGS)⌝ -∗
          ownGoState (hG := L'.goose_go_stateGS) ∅ ={⊤}=∗ P L')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ P
    ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    -- the start resources of `[fsExt]` are the filesystem's
    have Hl : extsLocalStart (GF := GF) σ.world ⊢
        [∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF) :=
      sep_elim_left
    iintro _ Hfiles Hgs
    iapply Hstart HN HT Hlctx $$ [Hfiles] Hgs
    iapply Hl $$ Hfiles
  · intro hG HN HT Hlctx
    iintro HP Htok
    imod Hwp HN HT Hlctx $$ HP Htok with ⟨Hwp, Hcrash⟩
    imodintro
    iframe Hwp
    iintro %L' Hcr Hcs Hgs
    -- the crash resources of `[fsExt]` are the filesystem's
    have Hc : extsCrashStart (GF := GF) hG.goose_localGS L' ⊢
        ⌜extLocalGS fsExt (L := L') = extLocalGS fsExt (L := hG.goose_localGS)⌝ :=
      sep_elim_left
    icases Hc $$ Hcs with %Hfs
    iapply Hcrash $$ %L' Hcr %Hfs Hgs

end Perennial
