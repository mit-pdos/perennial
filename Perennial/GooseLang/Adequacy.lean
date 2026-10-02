/-
Adequacy for GooseLang. Port of `src/goose_lang/adequacy.v` together with the
non-crash ("failstop") parts of `src/goose_lang/recovery_adequacy.v`.

Differences from the Rocq version:
* No crash logic: `ffi_interp_adequacy` has no `ffi_crash` obligation, and
  `gooseGpreS` has no `crashGpreS`. The adequacy theorem is the plain
  (non-recovery) one, built on iris-lean's `wp_adequacy`.
* Rocq's `ffi_global_start`/`ffi_local_start` live in `ffi_interp`; here
  (as `ffi_interp` in `Lifting.lean` omits them) they are fields of
  `ffi_interp_adequacy`.
* iris-lean has no `gFunctors` lists: `heapΣ`/`subG_heapPreG` have no
  counterpart; `gooseGpreS GF` is assumed directly.
* Later credits are part of iris-lean's `InvGpreS`.
-/
import Iris.ProgramLogic.Adequacy
import Perennial.GooseLang.Lifting

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

attribute [local instance] gset.lawfulSet

/-- What an FFI must provide to obtain an adequacy theorem: how to allocate its
ghost state for valid initial states. -/
class ffi_interp_adequacy (ffi : ffi_model) [FFI : ffi_interp ffi] where
  ffiGpreS : BundledGFunctors → Type
  ffi_initgP : ffi_global_state → Prop
  /-- Valid local starting states may depend on whatever the current global
  state is. -/
  ffi_initP : ffi_state → ffi_global_state → Prop
  /-- Resources handed to the program for the initial global FFI state. -/
  ffi_global_start : ∀ {GF : BundledGFunctors}, @ffiGlobalGS ffi FFI GF → ffi_global_state → IProp GF
  /-- Resources handed to the program for the initial local FFI state. -/
  ffi_local_start : ∀ {GF : BundledGFunctors}, @ffiLocalGS ffi FFI GF → ffi_state → IProp GF
  ffi_global_init : ∀ (GF : BundledGFunctors) (_hPre : ffiGpreS GF) (g : ffi_global_state),
    ffi_initgP g →
    ⊢@{IProp GF} |==> ∃ hG : @ffiGlobalGS ffi FFI GF, ffi_global_ctx hG g ∗ ffi_global_start hG g
  ffi_local_init : ∀ (GF : BundledGFunctors) (_hPre : ffiGpreS GF) (σ : ffi_state)
    (g : ffi_global_state), ffi_initP σ g →
    ⊢@{IProp GF} |==> ∃ hL : @ffiLocalGS ffi FFI GF, ffi_local_ctx hL σ ∗ ffi_local_start hL σ

export ffi_interp_adequacy (ffiGpreS ffi_initgP ffi_initP ffi_global_start ffi_local_start
  ffi_global_init ffi_local_init)

/-- The ghost state needed to instantiate the GooseLang program logic. -/
class gooseGpreS [ext : ffi_syntax] (ffi : ffi_model) [ffi_interp ffi] [ffi_interp_adequacy ffi]
    (GF : BundledGFunctors) where
  goose_preG_iris : InvGpreS GF
  goose_preG_heap : na_heapGpreS loc val GF
  goose_preG_proph : prophMapPreS proph_id val GF (gmap proph_id)
  goose_preG_ffi : ffiGpreS (ffi := ffi) GF
  goose_preG_go_state : go_state_preG GF

attribute [reducible, instance] gooseGpreS.goose_preG_iris gooseGpreS.goose_preG_heap
  gooseGpreS.goose_preG_proph gooseGpreS.goose_preG_go_state

section adequacy
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_interp_adequacy ffi]
variable [ffi_semantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- Allocate all of GooseLang's ghost state for an initial configuration, and
run a WP proof under it. This is the common core of the adequacy theorems. -/
theorem goose_init [hPre : gooseGpreS ffi GF] [Hinv : InvGS_gen .hasLC GF]
    (σ : state) (g : global_state) (κs : List observation)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (P : heapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      hG.goose_globalGS.goose_invGS = Hinv →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗ P hG) :
    ⊢@{IProp GF} |={⊤}=> ∃ hG : heapGS .hasLC GF,
      ⌜hG.goose_globalGS.goose_invGS = Hinv⌝ ∗
      goose_state_interp (σ, g) κs ∗ P hG := by
  imod na_heap_init (L := loc) (V := val)
    (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
  imod ProphMap.init (H := gmap proph_id) (V := val) κs g.used_proph_id with ⟨%hProph, Hp⟩
  imod go_state_init hPre.goose_preG_go_state σ.go_state.package_state with ⟨%γ, Hgs, Hgs'⟩
  imod ffi_global_init GF hPre.goose_preG_ffi g.global_world Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod ffi_local_init GF hPre.goose_preG_ffi σ.world g.global_world Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  let G : gooseGlobalGS .hasLC GF := ⟨Hinv, hProph, hFG⟩
  let L : gooseLocalGS GF :=
    ⟨hFL, σ.go_state.go_lctx, hHeap, go_stateGS_update_pre GF hPre.goose_preG_go_state γ⟩
  let hG : heapGS .hasLC GF := ⟨G, L⟩
  imod (@Hwp hG rfl rfl) $$ Hgstart Hlstart Hgs' with HP
  imodintro
  iexists hG
  isplitr
  · ipureintro; rfl
  iframe HP
  unfold goose_state_interp
  iframe
  ipureintro; rfl

/-- Adequacy of GooseLang: a WP proved for `e` under any instantiation of the
GooseLang ghost state (given the FFI's start resources and the initial package
state) implies that `e` does not get stuck and its result satisfies `φ`
(Rocq `goose_recv_adequacy_failstop`). -/
theorem goose_adequacy [hPre : gooseGpreS ffi GF]
    (e : expr) (σ : state) (g : global_state) (φ : val → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate Stuckness.NotStuck e ((σ, g) : cfg_state) (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) Stuckness.NotStuck e ((σ, g) : cfg_state) φ ?_
  intro Hinv κs
  imod goose_init (Hinv := Hinv) σ g κs Hinitg Hinit
    (fun (_ : heapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}))
    (@fun hG HinvEq Hlctx => by subst HinvEq; exact Hwp (hG := hG) Hlctx) with ⟨%hG, %HinvEq, Hσ, Hwp⟩
  imodintro
  iexists (fun σ κs => goose_state_interp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi⟩, L⟩ := hG
  cases HinvEq
  iexact Hwp

/-- Invariance: under the same hypotheses as `goose_adequacy`, a state
property that follows from the FFI's global interpretation holds in every
reachable configuration. -/
theorem goose_invariance [hPre : gooseGpreS ffi GF]
    (e : expr) (σ : state) (g : global_state) (φinv : ffi_global_state → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffi_global_ctx (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {t2 : List expr} {σ2 : cfg_state}
    (Hsteps : ([e], ((σ, g) : cfg_state)) -·->ₜₚ* (t2, σ2)) :
    φinv σ2.2.global_world := by
  refine wp_invariance (GF := GF) Stuckness.NotStuck e ((σ, g) : cfg_state) σ2 t2 _ ?_ Hsteps
  intro Hinv κs
  imod goose_init (Hinv := Hinv) σ g κs Hinitg Hinit
    (fun (_ : heapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffi_global_ctx (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝)))
    (@fun hG HinvEq Hlctx => by subst HinvEq; exact Hwp (hG := hG) Hlctx) with ⟨%hG, %HinvEq, Hσ, Hwp, Hφ⟩
  imodintro
  iexists (fun σ κs _ => goose_state_interp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi⟩, L⟩ := hG
  cases HinvEq
  isplitl [Hwp]
  · iexact Hwp
  iintro Hσ2
  iexists ∅
  unfold goose_state_interp
  icases Hσ2 with ⟨-, -, -, -, Hg, -⟩
  iapply Hφ $$ Hg

end adequacy

end Perennial
