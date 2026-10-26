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
/-- `bootStart` for `[fsExt]`: on the first boot, the ownership of the initial
files; after the crash of the generation `L`, its crash frame, its `crashed`
and that the files' ghost state is `L`'s (so that `L`'s `f fs↦ c`, in the crash
frame, describe the files after the crash). -/
def fsBootStart [GoGlobalContext] {GF : BundledGFunctors} (Ψ : HeapGS .hasLC GF → IProp GF)
    (σ : state) [hG : HeapGS .hasLC GF] : Option (GooseLocalGS GF) → IProp GF
  | none => iprop(([∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF)) ∗
      ownGoState σ.goState.packageState)
  | some L => iprop(Ψ ⟨hG.goose_globalGS, L⟩ ∗ crashed (hC := L.goose_crashGS) ∗
      ⌜extLocalGS fsExt (L := hG.goose_localGS) = extLocalGS fsExt (L := L)⌝ ∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅)

open fs_ext in
/-- Crash adequacy for a filesystem boot program `e` (`goose_crash_adequacy`
for `[fsExt]`): every boot proves the WP of `e` and its generation's crash
frame `Ψ` from `fsBootStart Ψ σ prev`. -/
theorem fs_crash_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS GF] (N T : Nat) (e : Expr) (σ : state) (g : GlobalState)
    (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p)) (Ψ : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF] (prev : Option (GooseLocalGS GF)),
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ fsBootStart Ψ σ prev -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T e σ g φ hφ ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ Ψ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  intro hG prev HN HT Hlctx
  cases prev with
  | none =>
    -- the start resources of `[fsExt]` are the filesystem's
    have Hl : extsLocalStart (GF := GF) σ.world ⊢
        [∗map] f ↦ c ∈ extLocal fsExt σ.world, (f fs↦ c : IProp GF) :=
      sep_elim_left
    dsimp only [bootStart]
    iintro ⟨_, Hfiles, Hgs⟩ Htok
    iapply Hwp none HN HT Hlctx $$ [Hfiles Hgs] Htok
    dsimp only [fsBootStart]
    iframe Hgs
    iapply Hl $$ Hfiles
  | some L =>
    -- the crash resources of `[fsExt]` are the filesystem's
    have Hc : extsCrashStart (GF := GF) L hG.goose_localGS ⊢
        ⌜extLocalGS fsExt (L := hG.goose_localGS) = extLocalGS fsExt (L := L)⌝ :=
      sep_elim_left
    dsimp only [bootStart]
    iintro ⟨HΨ, Hcr, Hcs, Hgs⟩ Htok
    icases Hc $$ Hcs with %Hfs
    iapply Hwp (some L) HN HT Hlctx $$ [HΨ Hcr Hgs] Htok
    dsimp only [fsBootStart]
    iframe
    ipureintro; exact Hfs

end Perennial
