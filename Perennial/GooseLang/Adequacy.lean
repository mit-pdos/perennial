/-
Adequacy for GooseLang (non-crash, "failstop").

Notes:
* No crash logic: `FfiInterpAdequacy` has no crash obligations. The adequacy
  theorem is the plain (non-recovery) one, built on iris-lean's `wp_adequacy`.
* `ffiGlobalStart`/`ffiLocalStart` are fields of `FfiInterpAdequacy`, not of
  `FfiInterp` (`Lifting.lean`).
* The ghost-state preconditions are the class `GooseGpreS ffi GF`, assumed
  directly by the adequacy theorems.
* Later credits are part of iris-lean's `InvGpreS`.
* Time receipts. The program logic is built for the step-bounded
  language of `BoundedLang.lean`; `goose_adequacy_blang` is its adequacy
  theorem. Every theorem here takes the time-receipt bound `N` as an argument:
  the receipt ghost state is allocated with `receiptBound GF = N` (handed to
  `Hwp` as a hypothesis, so a WP proof may assume anything it needs about `N`,
  such as `N ≤ 2^48`, as long as the client's `N` satisfies it) and the bounded
  semantics starts with step fuel `N - 1`. The main theorems `goose_adequacy`
  and `goose_invariance` are about the *real* semantics (`RealNsteps`,
  `gooseRealEctxiLang`) and conclude for executions of fewer than `N` steps
  (for `N = 0` they are vacuous); they follow from the bounded ones by the
  simulation `bounded_nsteps_of_real`. `gooseGpreS` also allocates the receipt
  ghost state (`goose_preG_receipt`), which does not depend on `N`.
* Thread tokens. Likewise every theorem takes the thread bound `T`: the thread
  ghost state is allocated with `threadBound GF = T` (also a hypothesis of
  `Hwp`, which moreover receives the main thread's token `threadTok`), the
  bounded semantics starts with thread fuel `T - 2` (the other `T - 1` tokens
  less the main thread's), and the real theorems are about executions whose
  thread count `GlobalState.threads` stays below `T` (`RealThreadsBelow`),
  started from a configuration with the main thread only (`g.threads = 1`).
  For `T ≤ 1` they are vacuous. See `Threads.lean`.
-/
module

public import Iris.ProgramLogic.Adequacy
public import Perennial.GooseLang.Lifting
public import Perennial.GooseLang.Countable

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

attribute [local instance] GSet.lawfulSet

/-- What an FFI must provide to obtain an adequacy theorem: how to allocate its
ghost state for valid initial states. -/
class FfiInterpAdequacy (ffi : FfiModel) [FFI : FfiInterp ffi] where
  ffiGpreS : BundledGFunctors → Type
  ffi_initgP : ffi_global_state → Prop
  /-- Valid local starting states may depend on whatever the current global
  state is. -/
  ffi_initP : ffi_state → ffi_global_state → Prop
  /-- Resources handed to the program for the initial global FFI state. -/
  ffiGlobalStart : ∀ {GF : BundledGFunctors}, @ffiGlobalGS ffi FFI GF → ffi_global_state → IProp GF
  /-- Resources handed to the program for the initial local FFI state. -/
  ffiLocalStart : ∀ {GF : BundledGFunctors}, @ffiLocalGS ffi FFI GF → ffi_state → IProp GF
  ffi_global_init : ∀ (GF : BundledGFunctors) (_hPre : ffiGpreS GF) (g : ffi_global_state),
    ffi_initgP g →
    ⊢@{IProp GF} |==> ∃ hG : @ffiGlobalGS ffi FFI GF, ffiGlobalCtx hG g ∗ ffiGlobalStart hG g
  ffi_local_init : ∀ (GF : BundledGFunctors) (_hPre : ffiGpreS GF) (σ : ffi_state)
    (g : ffi_global_state), ffi_initP σ g →
    ⊢@{IProp GF} |==> ∃ hL : @ffiLocalGS ffi FFI GF, ffiLocalCtx hL σ ∗ ffiLocalStart hL σ

export FfiInterpAdequacy (ffiGpreS ffi_initgP ffi_initP ffiGlobalStart ffiLocalStart
  ffi_global_init ffi_local_init)

/-- The ghost state needed to instantiate the GooseLang program logic. -/
class GooseGpreS [ext : FfiSyntax] (ffi : FfiModel) [FfiInterp ffi] [FfiInterpAdequacy ffi]
    (GF : BundledGFunctors) where
  goose_preG_iris : InvGpreS GF
  goose_preG_heap : NaHeapGpreS Loc val GF
  goose_preG_proph : prophMapPreS proph_id val GF (GMap proph_id)
  goosePreGFfi : ffiGpreS (ffi := ffi) GF
  goose_preG_go_state : GoStatePreG GF
  goose_preG_receipt : ReceiptGpreS GF
  goose_preG_thread : ThreadGpreS GF

attribute [reducible, instance] GooseGpreS.goose_preG_iris GooseGpreS.goose_preG_heap
  GooseGpreS.goose_preG_proph GooseGpreS.goose_preG_go_state GooseGpreS.goose_preG_receipt
  GooseGpreS.goose_preG_thread

section adequacy
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiInterpAdequacy ffi]
variable [FfiSemantics ext ffi] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- Allocate all of GooseLang's ghost state for an initial configuration, and
run a WP proof under it. This is the common core of the adequacy theorems. -/
theorem goose_init [hPre : GooseGpreS ffi GF] [Hinv : InvGS_gen .hasLC GF]
    (N T : Nat) (hN : 0 < N) (hT : 1 < T) (σ : state) (g : GlobalState) (κs : List Observation)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (P : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      hG.goose_globalGS.gooseInvGS = Hinv →
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗ P hG) :
    ⊢@{IProp GF} |={⊤}=> ∃ hG : HeapGS .hasLC GF,
      ⌜hG.goose_globalGS.gooseInvGS = Hinv⌝ ∗
      gooseBstateInterp (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) κs ∗ P hG := by
  imod na_heap_init (L := Loc) (V := val)
    (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
  imod ProphMap.init (H := GMap proph_id) (V := val) κs g.usedProphId with ⟨%hProph, Hp⟩
  imod goState_init hPre.goose_preG_go_state σ.goState.packageState with ⟨%γ, Hgs, Hgs'⟩
  imod ffi_global_init GF hPre.goosePreGFfi g.globalWorld Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod ffi_local_init GF hPre.goosePreGFfi σ.world g.globalWorld Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  imod receipt_init (hPre := hPre.goose_preG_receipt) N hN with ⟨%γR, %γL, HR⟩
  imod thread_init (hPre := hPre.goose_preG_thread) T hT with ⟨%γT, HT⟩
  let G : GooseGlobalGS .hasLC GF :=
    ⟨Hinv, hProph, hFG, ⟨hPre.goose_preG_receipt.receiptPreGAllG, γR, γL, N, hN⟩,
      ⟨hPre.goose_preG_thread.threadPreGAllG, γT, T, hT⟩⟩
  let L : GooseLocalGS GF :=
    ⟨hFL, σ.goState.goLctx, hHeap, goStateGSUpdatePre GF hPre.goose_preG_go_state γ⟩
  let hG : HeapGS .hasLC GF := ⟨G, L⟩
  -- the main thread's token and the thread fuel
  have Hsplit := (threadToks_add (hT := ⟨hPre.goose_preG_thread.threadPreGAllG, γT, T, hT⟩)
    (T - 2) 1).1
  rw [show T - 2 + 1 = T - 1 by omega] at Hsplit
  icases Hsplit $$ HT with ⟨Hfuel, Htok⟩
  imod (@Hwp hG rfl rfl rfl rfl) $$ Hgstart Hlstart Hgs' Htok with HP
  imodintro
  iexists hG
  isplitr
  · ipureintro; rfl
  iframe HP
  unfold gooseBstateInterp gooseStateInterp threadFuel
  iframe
  ipureintro; rfl

/-- Adequacy of the bounded GooseLang language (the one the program logic is
built for): a WP proved for `e` under any instantiation of the GooseLang ghost
state with time-receipt bound `N` and thread bound `T` (given the FFI's start
resources, the initial package state and the main thread's token) implies that
`e` does not get stuck and its result satisfies `φ`, in the bounded semantics
started with step fuel `N - 1` and thread fuel `T - 2`. See `goose_adequacy`
for the real semantics. -/
theorem goose_adequacy_blang [hPre : GooseGpreS ffi GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate Stuckness.NotStuck e (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF) Stuckness.NotStuck e (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) φ ?_
  intro Hinv κs
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (_ : HeapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}))
    (@fun hG HinvEq HN HT Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN HT Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp⟩
  imodintro
  iexists (fun σ κs => gooseBstateInterp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi, Grcpt, Gthr⟩, L⟩ := hG
  cases HinvEq
  iexact Hwp

/-- Adequacy of GooseLang, for the real semantics, under the time-receipt and
thread-bound assumptions: for any bounds `N` and `T`, if the WP is proved for
receipt bound `N` and thread bound `T` (`Hwp` may assume `receiptBound GF = N`
and `threadBound GF = T`, and receives the main thread's token), then in every
real execution of `e` of fewer than `N` steps, from a configuration with the
main thread only (`g.threads = 1`), along which fewer than `T` threads are live
(`RealThreadsBelow T n`: every configuration reachable in at most `n` steps has
`threads < T`), every thread is a value or can take a step, and if the main
thread has terminated with `v` then `φ v`. -/
theorem goose_adequacy [hPre : GooseGpreS ffi GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : g.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  have Hadeq := goose_adequacy_blang N T (by omega) hT e σ g φ Hinitg Hinit Hwp
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  have Hreach : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* (t2, (σ2, ⟨c, t⟩)) :=
    (Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩
  refine ⟨?_, ?_⟩
  · rintro v t2' rfl
    exact Hadeq.adequate_result t2' (σ2, ⟨c, t⟩) v Hreach
  · intro e2 he2
    exact realNotStuck_of_bounded (Hadeq.adequate_not_stuck t2 (σ2, ⟨c, t⟩) e2 rfl Hreach he2)

/-- Invariance for the bounded language: under the same hypotheses as
`goose_adequacy`, a state property that follows from the FFI's global
interpretation holds in every reachable configuration of the bounded semantics. -/
theorem goose_invariance_blang [hPre : GooseGpreS ffi GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e : Expr) (σ : state) (g : GlobalState) (φinv : ffi_global_state → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffiGlobalCtx (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {t2 : List Expr} {σ2 : BcfgState}
    (Hsteps : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* (t2, σ2)) :
    φinv σ2.1.2.globalWorld := by
  refine wp_invariance (GF := GF) Stuckness.NotStuck e (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) σ2
    t2 _ ?_ Hsteps
  intro Hinv κs
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (_ : HeapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffiGlobalCtx (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝)))
    (@fun hG HinvEq HN HT Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN HT Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp, Hφ⟩
  imodintro
  iexists (fun σ κs _ => gooseBstateInterp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun _ => iprop(True))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gffi, Grcpt, Gthr⟩, L⟩ := hG
  cases HinvEq
  isplitl [Hwp]
  · iexact Hwp
  iintro Hσ2
  iexists ∅
  unfold gooseBstateInterp gooseStateInterp
  icases Hσ2 with ⟨⟨-, -, -, -, Hg, -⟩, -⟩
  iapply Hφ $$ Hg

/-- Invariance (real semantics): under the same hypotheses as `goose_adequacy`,
a state property that follows from the FFI's global interpretation holds in
every configuration reachable by a real execution of fewer than `N` steps
along which fewer than `T` threads are live. -/
theorem goose_invariance [hPre : GooseGpreS ffi GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φinv : ffi_global_state → Prop)
    (Hinitg : ffi_initgP g.globalWorld) (Hinit : ffi_initP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ ffiGlobalStart (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g.globalWorld -∗
        ffiLocalStart (gooseFfiLocalGS (ffi := ffi) (GF := GF)) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', ffiGlobalCtx (gooseFfiGlobalGS (ffi := ffi) (GF := GF)) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : CfgState}
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : g.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    φinv σ2.2.globalWorld := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  exact goose_invariance_blang (σ2 := (σ2, ⟨c, t⟩)) N T (by omega) hT e σ g φinv Hinitg Hinit Hwp
    ((Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩)

end adequacy

end Perennial
