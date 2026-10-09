/-
Adequacy for the Grove FFI.

* There is no crash obligation in `grove_interp_adequacy`.
* Two (fail-stop) theorems: `grove_ffi_single_node_adequacy` for one node, and
  `grove_ffi_dist_adequacy` for a distributed system of nodes communicating
  over the network (the semantics of `DistLang.lean`, the generic theorem
  `goose_dist_adequacy` of `DistAdequacy.lean`).
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.DistAdequacy
public import Perennial.GooseLang.Ffi.GroveFfi.GroveFfi

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

attribute [local instance] grove_op grove_model grove_semantics grove_interp

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
/-- Adequacy for a single Grove node (fail-stop). The proof gets ownership of the
initial network and of the node's initial files. As for `goose_adequacy`, the
WP is proved for an arbitrary time-receipt bound `N` (`receiptBound GF = N`)
and the conclusion is about real executions of fewer than `N` steps. -/
theorem grove_ffi_single_node_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS grove_model GF] (N : Nat) (e : Expr) (σ : state) (g : GlobalState)
    (φ : val → Prop)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ([∗map] e ↦ ms ∈ g.globalWorld.groveNet, (e c↦ ms : IProp GF)) -∗
        ([∗map] f ↦ c ∈ σ.world.groveNodeFiles, (f f↦ c : IProp GF)) -∗
        ownGoState σ.goState.packageState ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) :=
  goose_adequacy N e σ g φ trivial trivial Hwp n κs t2 σ2 Hsteps Hbound

open grove_ffi in
open scoped DistGlobal in
/-- Adequacy for a distributed system of Grove nodes (fail-stop): node `i` runs
`ebσs[i].1` from local state `ebσs[i].2`. The proof gets ownership of the
initial network, from which it must provide, for every node and under any local
ghost state for it, a (not-stuck) WP for the node's program given the node's
initial files and package state. As for `goose_adequacy`, the WPs are proved for
an arbitrary time-receipt bound `N` (`receiptBound GF = N`), and the conclusion
is about real distributed executions of fewer than `N` steps (in total, over all
nodes): no thread of any node is stuck. -/
theorem grove_ffi_dist_adequacy [GoGlobalContext] {GF : BundledGFunctors}
    [hPre : GooseGpreS grove_model GF] (N : Nat) (ebσs : List (Expr × state))
    (g : GlobalState)
    (Hwp : ∀ [G : GooseGlobalGS .hasLC GF],
      receiptBound GF = N →
      ⊢ ([∗map] e ↦ ms ∈ g.globalWorld.groveNet, (e c↦ ms : IProp GF)) ={⊤}=∗
        ([∗list] ebσ ∈ ebσs, ∀ L : GooseLocalGS GF,
          ⌜L.goose_go_local_context = ebσ.2.goState.goLctx⌝ -∗
          (letI : HeapGS .hasLC GF := ⟨G, L⟩
           iprop(([∗map] f ↦ c ∈ ebσ.2.world.groveNodeFiles, (f f↦ c : IProp GF)) -∗
            ownGoState ebσ.2.goState.packageState ={⊤}=∗
            ∃ Φ : val → IProp GF, WP ebσ.1 @ Stuckness.NotStuck; ⊤ {{ Φ }})))) :
    DistAdequate N ebσs g :=
  goose_dist_adequacy N ebσs g trivial (fun _ _ => trivial) (fun hN => Hwp hN)

end Perennial
