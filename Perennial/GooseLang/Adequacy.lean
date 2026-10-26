/-
Adequacy for GooseLang (non-crash, "failstop").

Notes:
* These theorems are about executions without crashes, built on iris-lean's
  `wp_adequacy`; the crash adequacy theorem is `goose_crash_adequacy`
  (`CrashAdequacy.lean`).
* The theorems are generic over the closed list of extensions: they allocate
  each extension's ghost state (`ExtInterp.global_init`/`local_init`) and hand
  the program the start resources of all of them (`extsGlobalStart`,
  `extsLocalStart`).
* The ghost-state preconditions are the class `GooseGpreS GF`, assumed
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
  simulation `bounded_nsteps_of_real`. The receipt ghost state is allocated
  from `gooseGpreS`'s `AllG GF` (`goosePreGAllG`), which does not depend on `N`.
* Thread tokens. Likewise every theorem takes the thread bound `T`: the thread
  ghost state is allocated with `threadBound GF = T` (also a hypothesis of
  `Hwp`, which moreover receives the main thread's token `threadTok`), the
  bounded semantics starts with thread fuel `T - 2` (the other `T - 1` tokens
  less the main thread's), and the real theorems are about executions whose
  thread count `state.threads` stays below `T` (`RealThreadsBelow`),
  started from a configuration with the main thread only (`σ.threads = 1`).
  For `T ≤ 1` they are vacuous. See `Threads.lean`.
* Panics. A thread's final value may be a panic `PanicV p`: the main thread's is
  constrained by the client's `φ`, which `goose_adequacy` requires to exclude
  panics (`hφ : ∀ p, ¬ φ (PanicV p)`), and a forked thread's by `forkPost`
  (`goose_irisGS`: not a panic, `wp_fork`). `goose_adequacy` concludes that no
  thread has an unrecovered panic (`UnrecoveredPanic`), finished or still
  unwinding: an unwinding thread reaches `PanicV p` in the bounded language
  without using fuel (`goose_no_unrecovered_panic_blang`).
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

section exts
variable [GooseExts] [GooseInterp] {hlc : HasLC} {GF : BundledGFunctors}

/-- The initial global states of the extensions are valid. -/
abbrev extsInitgP (g : ExtsGlobalState exts) : Prop := Exts.initgP exts GooseInterp.interps g

/-- The initial local states of the extensions are valid. -/
abbrev extsInitP (σ : ExtsLocalState exts) (g : ExtsGlobalState exts) : Prop :=
  Exts.initP exts GooseInterp.interps σ g

/-- The resources of the extensions' initial global states. -/
abbrev extsGlobalStart [G : GooseGlobalGS hlc GF] (g : ExtsGlobalState exts) : IProp GF :=
  Exts.globalStart exts GooseInterp.interps G.gooseExtsGlobalGS g

/-- The resources of the extensions' initial local states. -/
abbrev extsLocalStart [L : GooseLocalGS GF] (σ : ExtsLocalState exts) : IProp GF :=
  Exts.localStart exts GooseInterp.interps L.gooseExtsLocalGS σ

end exts

/-- The ghost state needed to instantiate the GooseLang program logic. -/
class GooseGpreS [GooseExts] [GooseInterp] (GF : BundledGFunctors) where
  goose_preG_iris : InvGpreS GF
  goose_preG_heap : NaHeapGpreS Loc val GF
  goose_preG_proph : prophMapPreS proph_id val GF (GMap proph_id)
  /-- the ghost state of the extensions -/
  goosePreGExts : Exts.PreG exts GooseInterp.interps GF
  goose_preG_go_state : GoStatePreG GF
  /-- The `allG GF` of the `HeapGS` to be allocated (`GooseGlobalGS.gooseAllG`),
  from which the receipt and thread ghost state are allocated; not an instance,
  so that under the `HeapGS` of `Hwp` there is only that one -/
  goosePreGAllG : AllG GF

attribute [reducible, instance] GooseGpreS.goose_preG_iris GooseGpreS.goose_preG_heap
  GooseGpreS.goose_preG_proph GooseGpreS.goose_preG_go_state

section adequacy
variable [GooseExts] [GooseInterp]
variable [GooseSemantics] [GoGlobalContext]
variable {GF : BundledGFunctors}

/-- Allocate all of GooseLang's ghost state for an initial configuration, and
run a WP proof under it. This is the common core of the adequacy theorems. -/
theorem goose_init [hPre : GooseGpreS GF] [Hinv : InvGS_gen .hasLC GF]
    (N T : Nat) (hN : 0 < N) (hT : 1 < T) (σ : state) (g : GlobalState) (κs : List Observation)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (P : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      hG.goose_globalGS.gooseInvGS = Hinv →
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗ P hG) :
    ⊢@{IProp GF} |={⊤}=> ∃ hG : HeapGS .hasLC GF,
      ⌜hG.goose_globalGS.gooseInvGS = Hinv⌝ ∗
      gooseBstateInterp (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) κs ∗ P hG := by
  imod na_heap_init (L := Loc) (V := val)
    (hG := ⟨hPre.goose_preG_heap.na_heap_preG_inG, default⟩) tls σ.heap with ⟨%hHeap, Hh⟩
  imod ProphMap.init (H := GMap proph_id) (V := val) κs g.usedProphId with ⟨%hProph, Hp⟩
  imod goState_init hPre.goose_preG_go_state σ.goState.packageState with ⟨%γ, Hgs, Hgs'⟩
  imod Exts.global_init exts _ hPre.goosePreGExts g.globalWorld Hinitg with ⟨%hFG, Hgctx, Hgstart⟩
  imod Exts.local_init exts _ hPre.goosePreGExts σ.world g.globalWorld Hinit
    with ⟨%hFL, Hlctx, Hlstart⟩
  letI := hPre.goosePreGAllG
  imod receipt_init N hN with ⟨%γR, %γL, HR⟩
  imod thread_init T hT with ⟨%γT, HT⟩
  imod crashToken_init with ⟨%γC, HC⟩
  let G : GooseGlobalGS .hasLC GF :=
    ⟨Hinv, hPre.goosePreGAllG, hProph, hFG, ⟨γR, γL, N, hN⟩⟩
  let L : GooseLocalGS GF :=
    ⟨hFL, σ.goState.goLctx, hHeap, goStateGSUpdatePre GF hPre.goose_preG_go_state γ,
      ⟨γT, T, hT⟩, ⟨γC⟩⟩
  let hG : HeapGS .hasLC GF := ⟨G, L⟩
  -- the main thread's token and the thread fuel
  have Hsplit := (threadToks_add (hT := ⟨γT, T, hT⟩) (T - 2) 1).1
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
state with time-receipt bound `N` and thread bound `T` (given the extensions' start
resources, the initial package state and the main thread's token) implies that
`e` does not get stuck and its result satisfies `φ`, in the bounded semantics
started with step fuel `N - 1` and thread fuel `T - 2`. See `goose_adequacy`
for the real semantics. -/
theorem goose_adequacy_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
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
  iexists (fun v => iprop(⌜val.isPanic v = false⌝))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gext, Grcpt⟩, L⟩ := hG
  cases HinvEq
  iexact Hwp

/-- No thread of the bounded semantics ends in a panic: the main thread's
postcondition `φ` excludes panics (`hφ`; the convention for the main thread is
`φ (PanicV _) = False`), and a forked thread's final value satisfies `forkPost`
(`goose_irisGS`), which excludes panics (`wp_fork`). -/
theorem goose_adequacy_nopanic_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N)
    (hT : 1 < T) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : BcfgState}
    (Hsteps : Language.NSteps n ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) κs (t2, σ2))
    (v : val) (Hv : Val v ∈ t2) : v.isPanic = false := by
  refine wp_strong_adequacy (GF := GF) Stuckness.NotStuck [e]
    (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) n κs t2 σ2 (v.isPanic = false) (fun _ => 0) ?_ Hsteps
  intro Hinv
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (_ : HeapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }}))
    (@fun hG HinvEq HN HT Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN HT Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp⟩
  imodintro
  iexists (fun σ _ κs _ => gooseBstateInterp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists [fun v => iprop(⌜φ v⌝)]
  iexists (fun v => iprop(⌜val.isPanic v = false⌝))
  iexists (fun _ _ _ _ => fupd_intro)
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gext, Grcpt⟩, L⟩ := hG
  cases HinvEq
  isplitl [Hwp]
  · iapply BigSepL2.bigSepL2_singleton.2
    iexact Hwp
  iintro %es' %t2' %Heq %Hlen %_ _ Hes Hforks
  iapply fupd_mask_intro_discard Std.LawfulSet.empty_subset
  subst Heq
  obtain ⟨e', rfl⟩ : ∃ e', es' = [e'] := by
    match es', Hlen with
    | [e'], _ => exact ⟨e', rfl⟩
  rcases List.mem_append.1 Hv with Hv | Hv
  · obtain rfl : e' = Val v := (List.mem_singleton.1 Hv).symm
    icases BigSepL2.bigSepL2_singleton.1 $$ Hes with Hes
    simp only [ProgramLogic.ToVal.toVal, toVal, Option.elim_some]
    icases Hes with %Hφv
    ipureintro
    cases v <;> first | rfl | exact absurd Hφv (hφ _)
  · have Hmem : v ∈ List.filterMap toVal t2' := List.mem_filterMap.2 ⟨Val v, Hv, rfl⟩
    iapply (BigSepL.bigSepL_mem (Φ := fun v => iprop(⌜val.isPanic v = false⌝)) Hmem) $$ Hforks

/-- No thread of the bounded semantics has an unrecovered panic
(`UnrecoveredPanic`): such a thread would unwind to `PanicV p` without using fuel
(`unrecoveredPanic_steps`), contradicting `goose_adequacy_nopanic_blang`. -/
theorem goose_no_unrecovered_panic_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N)
    (hT : 1 < T) (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : BcfgState}
    (Hsteps : Language.NSteps n ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) κs (t2, σ2))
    (e2 : Expr) (He2 : e2 ∈ t2) : ¬ UnrecoveredPanic e2 := by
  intro Hu
  obtain ⟨p, Hp⟩ := unrecoveredPanic_steps Hu
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem He2
  have Hreach : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ*
      (t₁ ++ Val (PanicV p) :: t₂, σ2) :=
    ((Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hsteps⟩).trans (Hp [] t₁ t₂ σ2)
  obtain ⟨m, κs', Hm⟩ := (Language.erasedStep_nSteps _ _).mp Hreach
  have := goose_adequacy_nopanic_blang N T hN hT e σ g φ hφ Hinitg Hinit Hwp Hm (PanicV p)
    (by simp)
  simp at this

/-- Adequacy of GooseLang, for the real semantics, under the time-receipt and
thread-bound assumptions: for any bounds `N` and `T`, if the WP is proved for
receipt bound `N` and thread bound `T` (`Hwp` may assume `receiptBound GF = N`
and `threadBound GF = T`, and receives the main thread's token) with a
postcondition `φ` that excludes panics (`hφ`), then in every real execution of
`e` of fewer than `N` steps, from a configuration with the main thread only
(`σ.threads = 1`), along which fewer than `T` threads are live
(`RealThreadsBelow T n`: every configuration reachable in at most `n` steps has
`threads < T`):
* if the main thread has terminated with `v` then `φ v`;
* every thread is a value or can take a step;
* no thread has an unrecovered panic (`UnrecoveredPanic`): no thread has ended
  in a panic `PanicV p`, and none is unwinding one through frames none of which
  is a `Catch`. -/
theorem goose_adequacy [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }})
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState)
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧ (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  have Hadeq := goose_adequacy_blang N T (by omega) hT e σ g φ Hinitg Hinit Hwp
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  have Hreach : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* (t2, (σ2, ⟨c, t⟩)) :=
    (Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩
  refine ⟨?_, ?_, ?_⟩
  · rintro v t2' rfl
    exact Hadeq.adequate_result t2' (σ2, ⟨c, t⟩) v Hreach
  · intro e2 he2
    exact realNotStuck_of_bounded (Hadeq.adequate_not_stuck t2 (σ2, ⟨c, t⟩) e2 rfl Hreach he2)
  · exact goose_no_unrecovered_panic_blang N T (by omega) hT e σ g φ hφ Hinitg Hinit Hwp Hb

/-- Invariance for the bounded language: under the same hypotheses as
`goose_adequacy`, a state property that follows from the extensions' global
interpretation holds in every reachable configuration of the bounded semantics. -/
theorem goose_invariance_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e : Expr) (σ : state) (g : GlobalState) (φinv : ExtsGlobalState exts → Prop)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', extsGlobalCtx (GF := GF) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {t2 : List Expr} {σ2 : BcfgState}
    (Hsteps : ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) -·->ₜₚ* (t2, σ2)) :
    φinv σ2.1.2.globalWorld := by
  refine wp_invariance (GF := GF) Stuckness.NotStuck e (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState) σ2
    t2 _ ?_ Hsteps
  intro Hinv κs
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (_ : HeapGS .hasLC GF) => iprop(WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', extsGlobalCtx (GF := GF) g' ={⊤,∅}=∗ ⌜φinv g'⌝)))
    (@fun hG HinvEq HN HT Hlctx => by subst HinvEq; exact Hwp (hG := hG) HN HT Hlctx)
    with ⟨%hG, %HinvEq, Hσ, Hwp, Hφ⟩
  imodintro
  iexists (fun σ κs _ => gooseBstateInterp (G := hG.goose_globalGS) (L := hG.goose_localGS) σ κs)
  iexists (fun v => iprop(⌜val.isPanic v = false⌝))
  iframe Hσ
  obtain ⟨⟨Ginv, Gproph, Gext, Grcpt⟩, L⟩ := hG
  cases HinvEq
  isplitl [Hwp]
  · iexact Hwp
  iintro Hσ2
  iexists ∅
  unfold gooseBstateInterp gooseStateInterp
  icases Hσ2 with ⟨⟨-, -, -, -, Hg, -⟩, -, -, -⟩
  iapply Hφ $$ Hg

/-- Invariance (real semantics): under the same hypotheses as `goose_adequacy`,
a state property that follows from the extensions' global interpretation holds in
every configuration reachable by a real execution of fewer than `N` steps
along which fewer than `T` threads are live. -/
theorem goose_invariance [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φinv : ExtsGlobalState exts → Prop)
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ _v, True }} ∗
        (∀ g', extsGlobalCtx (GF := GF) g' ={⊤,∅}=∗ ⌜φinv g'⌝))
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : CfgState}
    (Hsteps : RealNsteps n ([e], ((σ, g) : CfgState)) κs (t2, σ2))
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealThreadsBelow T n ([e], ((σ, g) : CfgState))) :
    φinv σ2.2.globalWorld := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  exact goose_invariance_blang (σ2 := (σ2, ⟨c, t⟩)) N T (by omega) hT e σ g φinv Hinitg Hinit Hwp
    ((Language.erasedStep_nSteps _ _).mpr ⟨n, κs, Hb⟩)

end adequacy

end Perennial
