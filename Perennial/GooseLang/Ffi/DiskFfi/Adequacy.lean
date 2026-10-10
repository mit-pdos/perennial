/-
Adequacy for the disk FFI (`disk_interp_adequacy`), plus a disk-specific
instance of `goose_adequacy`. Crashes are not modeled: there is no crash
obligation and there are no `IntoCrash` instances.
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.Ffi.DiskFfi.Specs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- Adequacy of the disk FFI's ghost state interpretation. -/
instance disk_interp_adequacy : FfiInterpAdequacy disk_model where
  ffiGpreS := DiskPreG
  ffi_initgP _ := True
  ffi_initP _ _ := True
  ffiGlobalStart _ _ := iprop(True)
  ffiLocalStart hL d :=
    iprop([∗map] a ↦ b ∈ (d : DiskState), diskPointsto hL a (.own 1) b)
  ffi_global_init _ _ _ _ := by
    iapply bupd_intro
    iexists ()
    isplit
    · iapply (show iprop(True) ⊢ disk_interp.ffiGlobalCtx () _ from .rfl); itrivial
    · itrivial
  ffi_local_init GF hPre σ _ _ := by
    letI := hPre.diskPreGGenHeapG
    imod genHeap_init (H := GMap Int) (σ : DiskState) with ⟨%names, H1, H2, -⟩
    imodintro
    iexists (⟨names⟩ : DiskGS GF)
    iframe H1
    unfold diskPointsto
    iexact H2

open disk_ffi in
/-- Adequacy for GooseLang with the disk FFI: if the WP is proved for arbitrary
time-receipt and thread bounds `N` and `T` (`receiptBound GF = N`,
`threadBound GF = T`; the proof gets the main thread's token), then in every
real execution of fewer than `N` steps along which fewer than `T` threads are
live, no thread is stuck and a final value of the main thread satisfies `φ`
(see `goose_adequacy`). -/
theorem disk_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS disk_model GF] (N T : Nat) (e : Expr) (σ : state) (g : GlobalState)
    (φ : val → Prop)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] a ↦ b ∈ diskWorld σ, diskPointsto (gooseDiskGS (GF := GF)) a (.own 1) b) -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : g.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) := by
  refine goose_adequacy (GF := GF) N T e σ g φ trivial trivial ?_ n κs t2 σ2 Hsteps Hbound
    Hthreads Hlive
  intro hG HN HT Hlctx
  iintro _ Hd Hgs Htok
  iapply Hwp HN HT Hlctx $$ Hd Hgs Htok

end Perennial
