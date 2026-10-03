/-
Adequacy for the disk FFI. Port of the non-crash parts of
`src/goose_lang/ffi/disk_ffi/adequacy.v` (`disk_interp_adequacy`), plus a
disk-specific instance of `goose_adequacy`.

Differences from the Rocq version: no crash obligation, no `IntoCrash`
instances.
-/
import Perennial.GooseLang.Adequacy
import Perennial.GooseLang.Ffi.DiskFfi.Specs

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] disk_op disk_model disk_semantics disk_interp

/-- Rocq `disk_interp_adequacy`. -/
instance disk_interp_adequacy : ffi_interp_adequacy disk_model where
  ffiGpreS := disk_preG
  ffi_initgP _ := True
  ffi_initP _ _ := True
  ffi_global_start _ _ := iprop(True)
  ffi_local_start hL d :=
    iprop([∗map] a ↦ b ∈ (d : disk_state), disk_pointsto hL a (.own 1) b)
  ffi_global_init _ _ _ _ := by
    iapply bupd_intro
    iexists ()
    isplit
    · iapply (show iprop(True) ⊢ disk_interp.ffi_global_ctx () _ from .rfl); itrivial
    · itrivial
  ffi_local_init GF hPre σ _ _ := by
    letI := hPre.disk_preG_gen_heapG
    imod genHeap_init (H := gmap Int) (σ : disk_state) with ⟨%names, H1, H2, -⟩
    imodintro
    iexists (⟨names⟩ : diskGS GF)
    iframe H1
    unfold disk_pointsto
    iexact H2

open disk_ffi in
/-- Adequacy for GooseLang with the disk FFI: in every real execution of fewer
than `receipt_bound` steps, no thread is stuck and a final value of the main
thread satisfies `φ` (see `goose_adequacy`). -/
theorem disk_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : gooseGpreS disk_model GF] (e : expr) (σ : state) (g : global_state)
    (φ : val → Prop)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ([∗map] a ↦ b ∈ disk_world σ, disk_pointsto (goose_diskGS (GF := GF)) a (.own 1) b) -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List observation) (t2 : List expr) (σ2 : cfg_state)
    (Hsteps : real_nsteps n ([e], ((σ, g) : cfg_state)) κs (t2, σ2))
    (Hbound : n < receipt_bound) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → real_not_stuck e2 σ2) := by
  refine goose_adequacy (GF := GF) e σ g φ trivial trivial ?_ n κs t2 σ2 Hsteps Hbound
  intro hG Hlctx
  iintro _ Hd Hgs
  iapply Hwp Hlctx $$ Hd Hgs

end Perennial
