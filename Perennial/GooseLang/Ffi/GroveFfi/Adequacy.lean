/-
Adequacy for the Grove FFI. Port of the adequacy parts of
`src/goose_lang/ffi/grove_ffi/grove_ffi.v` (`grove_interp_adequacy`) and of
`src/goose_lang/ffi/grove_ffi/adequacy.v`.

Differences from the Rocq version:
* No crash obligation in `grove_interp_adequacy`.
* Only the single-node theorem (`grove_ffi_single_node_adequacy`, Rocq
  `grove_ffi_single_node_adequacy_failstop`) is ported. The distributed
  theorems (`grove_ffi_dist_adequacy`, `grove_ffi_dist_adequacy_failstop`)
  need the distributed-language machinery of `program_logic/dist_lang.v` and
  `goose_lang/dist_adequacy.v`, which is not ported.
-/
import Perennial.GooseLang.Adequacy
import Perennial.GooseLang.Ffi.GroveFfi.GroveFfi

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] grove_op grove_model grove_semantics grove_interp

/-- Rocq `grove_interp_adequacy`. -/
instance grove_interp_adequacy : ffi_interp_adequacy grove_model where
  ffiGpreS := groveGpreS
  ffi_initgP _ := True
  ffi_initP _ _ := True
  ffi_global_start hG g :=
    iprop([∗map] e ↦ ms ∈ g.grove_net, chan_pointsto hG e ms)
  ffi_local_start hL σ :=
    iprop([∗map] f ↦ c ∈ σ.grove_node_files, file_pointsto hL f (.own 1) c)
  ffi_global_init GF hPre g _ := by
    letI := hPre.grove_preG_net_heapG
    imod genHeap_init (H := gmap endpoint) g.grove_net with ⟨%names, H1, H2, -⟩
    imod @MonoNat.own_alloc GF hPre.grove_preG_tscG (MaxNat.ofNat g.grove_global_time.toNat)
      with ⟨%γ, Ht, -⟩
    imodintro
    iexists (⟨names, γ, hPre.grove_preG_tscG⟩ : groveGS GF)
    isplitl [H1 Ht]
    · iapply (grove_interp_global_ctx_eq _ _).mpr; iframe
    · unfold chan_pointsto; iexact H2
  ffi_local_init GF hPre σ _ _ := by
    letI := hPre.grove_preG_files_heapG
    imod @MonoNat.own_alloc GF hPre.grove_preG_tscG (MaxNat.ofNat σ.grove_node_tsc.toNat)
      with ⟨%γ, Htsc, -⟩
    imod genHeap_init (H := gmap byte_string) σ.grove_node_files with ⟨%names, H1, H2, -⟩
    imodintro
    iexists (⟨hPre, γ, names⟩ : groveNodeGS GF)
    isplitl [H1 Htsc]
    · iapply (grove_interp_local_ctx_eq _ _).mpr; iframe
    · unfold file_pointsto; iexact H2

open grove_ffi in
/-- Adequacy for a single Grove node (Rocq
`grove_ffi_single_node_adequacy_failstop`). The proof gets ownership of the
initial network and of the node's initial files. As for `goose_adequacy`, the
WP is proved for an arbitrary time-receipt bound `N` (`receipt_bound GF = N`)
and the conclusion is about real executions of fewer than `N` steps. -/
theorem grove_ffi_single_node_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : gooseGpreS grove_model GF] (N : Nat) (e : expr) (σ : state) (g : global_state)
    (φ : val → Prop)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ([∗map] e ↦ ms ∈ g.global_world.grove_net, (e c↦ ms : IProp GF)) -∗
        ([∗map] f ↦ c ∈ σ.world.grove_node_files, (f f↦ c : IProp GF)) -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List observation) (t2 : List expr) (σ2 : cfg_state)
    (Hsteps : real_nsteps n ([e], ((σ, g) : cfg_state)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → real_not_stuck e2 σ2) :=
  goose_adequacy N e σ g φ trivial trivial Hwp n κs t2 σ2 Hsteps Hbound

end Perennial
