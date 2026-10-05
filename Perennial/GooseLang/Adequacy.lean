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
* (Lean addition, time receipts) The program logic is built for the step-bounded
  language of `BoundedLang.lean`; `goose_adequacy_blang` is its adequacy
  theorem. Every theorem here takes the time-receipt bound `N` as an argument:
  the receipt ghost state is allocated with `receipt_bound GF = N` (handed to
  `Hwp` as a hypothesis, so a WP proof may assume anything it needs about `N`,
  such as `N ≤ 2^48`, as long as the client's `N` satisfies it) and the bounded
  semantics starts with fuel `N - 1`. The main theorems `goose_adequacy` and
  `goose_invariance` are about the *real* semantics (`real_nsteps`,
  `goose_real_ectxi_lang`) and conclude for executions of fewer than `N` steps
  (for `N = 0` they are vacuous); they follow from the bounded ones by the
  simulation `bounded_nsteps_of_real`. `gooseGpreS` also allocates the receipt
  ghost state (`goose_preG_receipt`), which does not depend on `N`.
-/
import Iris.ProgramLogic.Adequacy
import Perennial.GooseLang.Lifting
import Perennial.GooseLang.Countable

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
  goose_preG_receipt : receiptGpreS GF

attribute [reducible, instance] gooseGpreS.goose_preG_iris gooseGpreS.goose_preG_heap
  gooseGpreS.goose_preG_proph gooseGpreS.goose_preG_go_state gooseGpreS.goose_preG_receipt

section adequacy
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_interp_adequacy ffi]
variable [ffi_semantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- Allocate all of GooseLang's ghost state for an initial configuration, and
run a WP proof under it. This is the common core of the adequacy theorems. -/
theorem goose_init [hPre : gooseGpreS ffi GF] [Hinv : InvGS_gen .hasLC GF]
    (N : Nat) (hN : 0 < N) (σ : state) (g : global_state) (κs : List observation)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (P : heapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      hG.goose_globalGS.goose_invGS = Hinv →
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗ P hG) :
    ⊢@{IProp GF} |={⊤}=> ∃ hG : heapGS .hasLC GF,
      ⌜hG.goose_globalGS.goose_invGS = Hinv⌝ ∗
      goose_bstate_interp (((σ, g), N - 1) : bcfg_state) κs ∗ P hG := by
  imod na_heap_init (L := loc) (V := val)
    (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
  imod ProphMap.init (H := gmap proph_id) (V := val) κs g.used_proph_id with ⟨%hProph, Hp⟩
  imod go_state_init hPre.goose_preG_go_state σ.go_state.package_state with ⟨%γ, Hgs, Hgs'⟩
  imod ffi_global_init GF hPre.goose_preG_ffi g.global_world Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod ffi_local_init GF hPre.goose_preG_ffi σ.world g.global_world Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  imod receipt_init (hPre := hPre.goose_preG_receipt) N hN with ⟨%γR, HR⟩
  let G : gooseGlobalGS .hasLC GF :=
    ⟨Hinv, hProph, hFG, ⟨hPre.goose_preG_receipt.receipt_preG_allG, γR, N, hN⟩⟩
  let L : gooseLocalGS GF :=
    ⟨hFL, σ.go_state.go_lctx, hHeap, go_stateGS_update_pre GF hPre.goose_preG_go_state γ⟩
  let hG : heapGS .hasLC GF := ⟨G, L⟩
  imod (@Hwp hG rfl rfl rfl) $$ Hgstart Hlstart Hgs' with HP
  imodintro
  iexists hG
  isplitr
  · ipureintro; rfl
  iframe HP
  unfold goose_bstate_interp goose_state_interp
  iframe
  ipureintro; rfl

/-- Adequacy of the bounded GooseLang language (the one the program logic is
built for): a WP proved for `e` under any instantiation of the GooseLang ghost
state with time-receipt bound `N` (given the FFI's start resources and the
initial package state) implies that `e` does not get stuck and its result
satisfies `φ`, in the bounded semantics started with fuel `N - 1` (Rocq
`goose_recv_adequacy_failstop`). See `goose_adequacy` for the real semantics. -/
theorem goose_adequacy_blang [hPre : gooseGpreS ffi GF] (N : Nat) (hN : 0 < N)
    (e : expr) (σ : state) (g : global_state) (φ : val → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate Stuckness.NotStuck e (((σ, g), N - 1) : bcfg_state) (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) Stuckness.NotStuck e (((σ, g), N - 1) : bcfg_state) φ ?_
  intro Hinv κs
  imod goose_init (Hinv := Hinv) N hN σ g κs Hinitg Hinit
    (fun (_ : heapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}))
    (@fun hG HinvEq HN Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp⟩
  imodintro
  iexists (fun σ κs => goose_bstate_interp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi, Grcpt⟩, L⟩ := hG
  cases HinvEq
  iexact Hwp

/-- Adequacy of GooseLang (Rocq `goose_recv_adequacy_failstop`), for the real
semantics, under the time-receipt assumption: for any bound `N`, if the WP is
proved for receipt bound `N` (`Hwp` may assume `receipt_bound GF = N`), then
in every real execution of `e` of fewer than `N` steps, every thread is a
value or can take a step, and if the main thread has terminated with `v` then
`φ v`. -/
theorem goose_adequacy [hPre : gooseGpreS ffi GF] (N : Nat)
    (e : expr) (σ : state) (g : global_state) (φ : val → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List observation) (t2 : List expr) (σ2 : cfg_state)
    (Hsteps : real_nsteps n ([e], ((σ, g) : cfg_state)) κs (t2, σ2))
    (Hbound : n < N) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → real_not_stuck e2 σ2) := by
  have Hadeq := goose_adequacy_blang N (by omega) e σ g φ Hinitg Hinit Hwp
  obtain ⟨c, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega)
  have Hreach : ([e], (((σ, g), N - 1) : bcfg_state)) -·->ₜₚ* (t2, (σ2, c)) :=
    (Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩
  refine ⟨?_, ?_⟩
  · rintro v t2' rfl
    exact Hadeq.adequate_result t2' (σ2, c) v Hreach
  · intro e2 he2
    exact real_not_stuck_of_bounded (Hadeq.adequate_not_stuck t2 (σ2, c) e2 rfl Hreach he2)

/-- Invariance for the bounded language: under the same hypotheses as
`goose_adequacy`, a state property that follows from the FFI's global
interpretation holds in every reachable configuration of the bounded semantics. -/
theorem goose_invariance_blang [hPre : gooseGpreS ffi GF] (N : Nat) (hN : 0 < N)
    (e : expr) (σ : state) (g : global_state) (φinv : ffi_global_state → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffi_global_ctx (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {t2 : List expr} {σ2 : bcfg_state}
    (Hsteps : ([e], (((σ, g), N - 1) : bcfg_state)) -·->ₜₚ* (t2, σ2)) :
    φinv σ2.1.2.global_world := by
  refine wp_invariance (GF := GF) Stuckness.NotStuck e (((σ, g), N - 1) : bcfg_state) σ2 t2 _ ?_
    Hsteps
  intro Hinv κs
  imod goose_init (Hinv := Hinv) N hN σ g κs Hinitg Hinit
    (fun (_ : heapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffi_global_ctx (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝)))
    (@fun hG HinvEq HN Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp, Hφ⟩
  imodintro
  iexists (fun σ κs _ => goose_bstate_interp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi, Grcpt⟩, L⟩ := hG
  cases HinvEq
  isplitl [Hwp]
  · iexact Hwp
  iintro Hσ2
  iexists ∅
  unfold goose_bstate_interp goose_state_interp
  icases Hσ2 with ⟨⟨-, -, -, -, Hg, -⟩, -⟩
  iapply Hφ $$ Hg

/-- Invariance (real semantics): under the same hypotheses as `goose_adequacy`,
a state property that follows from the FFI's global interpretation holds in
every configuration reachable by a real execution of fewer than `N` steps. -/
theorem goose_invariance [hPre : gooseGpreS ffi GF] (N : Nat)
    (e : expr) (σ : state) (g : global_state) (φinv : ffi_global_state → Prop)
    (Hinitg : ffi_initgP g.global_world) (Hinit : ffi_initP σ.world g.global_world)
    (Hwp : ∀ [hG : heapGS .hasLC GF],
      receipt_bound GF = N →
      hG.goose_localGS.goose_go_local_context = σ.go_state.go_lctx →
      ⊢ ffi_global_start (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g.global_world -∗
        ffi_local_start (goose_ffiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        own_go_state σ.go_state.package_state ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffi_global_ctx (goose_ffiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {n : Nat} {κs : List observation} {t2 : List expr} {σ2 : cfg_state}
    (Hsteps : real_nsteps n ([e], ((σ, g) : cfg_state)) κs (t2, σ2))
    (Hbound : n < N) :
    φinv σ2.2.global_world := by
  obtain ⟨c, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega)
  exact goose_invariance_blang (σ2 := (σ2, c)) N (by omega) e σ g φinv Hinitg Hinit Hwp
    ((Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩)

end adequacy

end Perennial
