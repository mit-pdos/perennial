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

open fs_ext in
/-- Crash adequacy for a filesystem program `e` with recovery procedure `r`
(`goose_crash_adequacy` for `[fsExt]`): the program gets ownership of the
initial files, and the recovery procedure learns that the files' ghost state is
that of the crashed generation (so that the crash frame `Ψ` can carry the
files' points-to across the crash). -/
theorem fs_crash_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS GF] (N T : Nat) (e r : Expr) (σ : state) (g : GlobalState)
    (φ φr : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p)) (hφr : ∀ p, ¬ φr (PanicV p))
    (Ψ : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF)) -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG)
    (Hrec : ∀ (hG : HeapGS .hasLC GF) [hG' : HeapGS .hasLC GF],
      hG'.goose_globalGS = hG.goose_globalGS →
      receiptBound GF = N →
      threadBound GF = T →
      hG'.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      extLocalGS fsExt (L := hG'.goose_localGS) = extLocalGS fsExt (L := hG.goose_localGS) →
      ⊢ Ψ hG -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        ownGoState ∅ -∗ threadTok ={⊤}=∗
        WP r @ Stuckness.NotStuck; ⊤ {{ v, ⌜φr v⌝ }} ∗ Ψ hG')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps r n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow r T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → if b then φr v else φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T e r σ g φ φr hφ hφr ⟨trivial, trivial⟩
    ⟨trivial, trivial⟩ Ψ ?_ ?_ n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · intro hG HN HT Hlctx
    have Hl : extsLocalStart (GF := GF) σ.world ⊢
        [∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF) :=
      sep_elim_left
    iintro _ Hfiles Hgs Htok
    iapply Hwp HN HT Hlctx $$ [Hfiles] Hgs Htok
    iapply Hl $$ Hfiles
  · intro hG hG' HG HN HT Hlctx
    -- the crash resources of `[fsExt]` are the filesystem's
    have Hc : extsCrashStart (GF := GF) hG.goose_localGS hG'.goose_localGS ⊢
        ⌜extLocalGS fsExt (L := hG'.goose_localGS) = extLocalGS fsExt (L := hG.goose_localGS)⌝ :=
      sep_elim_left
    iintro HΨ Hcr Hcs Hgs Htok
    icases Hc $$ Hcs with %Hfs
    iapply Hrec hG HG HN HT Hlctx Hfs $$ HΨ Hcr Hgs Htok

end Perennial
