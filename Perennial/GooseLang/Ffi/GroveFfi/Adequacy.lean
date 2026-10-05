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
instance grove_interp_adequacy : FfiInterpAdequacy grove_model where
  ffiGpreS := GroveGpreS
  ffi_initgP _ := True
  ffi_initP _ _ := True
  ffiGlobalStart hG g :=
    iprop([∗map] e ↦ ms ∈ g.groveNet, chanPointsto hG e ms)
  ffiLocalStart hL σ :=
    iprop([∗map] f ↦ c ∈ σ.groveNodeFiles, filePointsto hL f (.own 1) c)
  ffi_global_init GF hPre g _ := by
    letI := hPre.grovePreGNetHeapG
    imod genHeap_init (H := GMap Endpoint) g.groveNet with ⟨%names, H1, H2, -⟩
    imod @MonoNat.own_alloc GF hPre.grovePreGTscG (MaxNat.ofNat g.groveGlobalTime.toNat)
      with ⟨%γ, Ht, -⟩
    imodintro
    iexists (⟨names, γ, hPre.grovePreGTscG⟩ : GroveGS GF)
    isplitl [H1 Ht]
    · iapply (grove_interp_global_ctx_eq _ _).mpr; iframe
    · unfold chanPointsto; iexact H2
  ffi_local_init GF hPre σ _ _ := by
    letI := hPre.grovePreGFilesHeapG
    imod @MonoNat.own_alloc GF hPre.grovePreGTscG (MaxNat.ofNat σ.groveNodeTsc.toNat)
      with ⟨%γ, Htsc, -⟩
    imod genHeap_init (H := GMap byte_string) σ.groveNodeFiles with ⟨%names, H1, H2, -⟩
    imodintro
    iexists (⟨hPre, γ, names⟩ : GroveNodeGS GF)
    isplitl [H1 Htsc]
    · iapply (grove_interp_local_ctx_eq _ _).mpr; iframe
    · unfold filePointsto; iexact H2

open grove_ffi in
/-- Adequacy for a single Grove node (Rocq
`grove_ffi_single_node_adequacy_failstop`). The proof gets ownership of the
initial network and of the node's initial files. As for `goose_adequacy`, the
WP is proved for an arbitrary time-receipt bound `N` (`receiptBound GF = N`)
and the conclusion is about real executions of fewer than `N` steps. -/
theorem grove_ffi_single_node_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS grove_model GF] (N : Nat) (e : expr) (σ : state) (g : GlobalState)
    (φ : val → Prop)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] e ↦ ms ∈ g.globalWorld.groveNet, (e c↦ ms : IProp GF)) -∗
        ([∗map] f ↦ c ∈ σ.world.groveNodeFiles, (f f↦ c : IProp GF)) -∗
        ownGoState σ.goState.packageState ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) :=
  goose_adequacy N e σ g φ trivial trivial Hwp n κs t2 σ2 Hsteps Hbound

end Perennial
