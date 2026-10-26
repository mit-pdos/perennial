/-
Crash adequacy for GooseLang: the adequacy of the standard (iris-lean) WP for
executions with crashes (`RealCrashNsteps`, `CrashLang.lean`).

Notes:
* An execution with crashes is a sequence of *generations*: the program `e`
  runs until the node crashes, then the recovery procedure `r` runs from the
  crashed state (`Crash`, `Lang.lean`) until the next crash, and so on. Each
  generation is a run of the standard WP; there is no crash WP. All the
  generations are one Iris proof: they share the global ghost state
  (`GooseGlobalGS`: invariants, the prophecy map, the extensions' global ghost
  state, time receipts), and each has its own local ghost state
  (`GooseLocalGS`: heap, package state, extensions' local ghost state, thread
  tokens, crash token).
* At a crash, the threads and the resources they own are gone; what crosses
  the crash is what lives outside of them: invariants, and the *crash frame*
  `Ψ` of the theorem, a resource that the proof of each generation sets aside
  for the next one. The adequacy proof performs the crash itself
  (`goose_crash_step`): it throws away the old generation's heap and package
  state, crashes the extensions' local ghost state
  (`ExtCrashInterp.local_crash`), allocates the new generation's local ghost
  state, and turns the old generation's `notCrashed` (owned by the state
  interpretation, `CrashToken.lean`) into its persistent `crashed`.
* `goose_crash_adequacy` is for a single boot program `e`, which runs at the
  start and after every crash. Its one premise proves, for any generation, the
  WP of `e` and the generation's crash frame from what the boot gives
  (`bootStart Ψ σ g prev`): on the first boot (`prev = none`) the extensions'
  start resources and the initial package state; after the crash of a
  generation `L` (`prev = some L`) `L`'s crash frame, `L`'s `crashed`, the
  extensions' `crashStart` resources relating `L` and the new generation, and
  the package state of a restarted program (none initialized).
  `goose_crash_adequacy_recovery`, from which it follows, allows a recovery
  procedure `r` other than `e`, with separate premises for the first boot
  (`Hwp`) and the others (`Hrec`).
* Every extension of the program must say how its ghost state survives a crash
  (`ExtCrashInterp`, collected in `GooseCrashInterp`).
* Time receipts bound the steps of all generations together (the step fuel
  survives a crash); thread tokens are per generation (the thread fuel is reset,
  and each generation's main thread has a new token). As for `goose_adequacy`,
  the theorem is about executions of fewer than `N` steps in all along which
  fewer than `T` threads are live (`RealCrashThreadsBelow`).
-/
module

public import Perennial.GooseLang.Adequacy
public import Perennial.GooseLang.CrashLang

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Language.Notation

attribute [local instance] GSet.lawfulSet

/-! ## What an extension's ghost state does at a crash -/

/-- How the ghost state of the extension `E` survives a crash: the
interpretation of the old local state gives way to that of the crashed state
(by `E`'s `ExtSemantics.crash`), under a new local ghost state, with the
resources `crashStart old new`, relating the two, for the recovery procedure. A
durable state may keep its ghost state (`crashStart old new := ⌜new = old⌝`),
so that the old generation's resources describe the new state. -/
class ExtCrashInterp (E : GooseExt) [S : ExtSemantics E] [I : ExtInterp E] where
  crashStart : ∀ {GF : BundledGFunctors}, I.LocalGS GF → I.LocalGS GF → IProp GF
  local_crash : ∀ (GF : BundledGFunctors) (_hPre : I.PreG GF) (hL : I.LocalGS GF)
    (σ σ' : E.LocalState), S.crash σ σ' →
    ⊢@{IProp GF} I.localCtx hL σ ==∗ ∃ hL' : I.LocalGS GF, I.localCtx hL' σ' ∗ crashStart hL hL'

namespace Exts
variable {GF : BundledGFunctors}

/-- An `ExtCrashInterp` for each extension of `l`. -/
def CrashInterp : (l : List GooseExt) → ExtTuple ExtSemantics l → ExtTuple ExtInterp l → Type 1
  | [], _, _ => PUnit
  | E :: l, Ss, Is => @ExtCrashInterp E Ss.1 Is.1 × CrashInterp l Ss.2 Is.2

def crashStart : (l : List GooseExt) → (Ss : ExtTuple ExtSemantics l) →
    (Is : ExtTuple ExtInterp l) → CrashInterp l Ss Is → LocalGS l Is GF → LocalGS l Is GF →
    IProp GF
  | [], _, _, _, _, _ => iprop(emp)
  | _ :: l, Ss, Is, Cs, gs, gs' =>
    iprop(@ExtCrashInterp.crashStart _ Ss.1 Is.1 Cs.1 GF gs.1 gs'.1 ∗
      crashStart l Ss.2 Is.2 Cs.2 gs.2 gs'.2)

theorem local_crash : (l : List GooseExt) → (Ss : ExtTuple ExtSemantics l) →
    (Is : ExtTuple ExtInterp l) → (Cs : CrashInterp l Ss Is) → (hPre : PreG l Is GF) →
    (gs : LocalGS l Is GF) → (w w' : ExtsLocalState l) → ExtsCrash l Ss w w' →
    ⊢@{IProp GF} localCtx l Is gs w ==∗
      ∃ gs' : LocalGS l Is GF, localCtx l Is gs' w' ∗ crashStart l Ss Is Cs gs gs'
  | [], _, _, _, _, _, _, _, _ => by
    iintro _
    iapply bupd_intro; iexists PUnit.unit; dsimp only [localCtx, crashStart]
    isplitl [] <;> iempintro
  | _ :: l, Ss, Is, Cs, hPre, gs, w, w', ⟨h1, h2⟩ => by
    dsimp only [localCtx]
    iintro ⟨H1, H2⟩
    imod @ExtCrashInterp.local_crash _ Ss.1 Is.1 Cs.1 GF hPre.1 gs.1 w.1 w'.1 h1 $$ H1
      with ⟨%gs1, Hc1, Hs1⟩
    imod local_crash l Ss.2 Is.2 Cs.2 hPre.2 gs.2 w.2 w'.2 h2 $$ H2 with ⟨%gs2, Hc2, Hs2⟩
    imodintro
    iexists ((gs1, gs2) : LocalGS (_ :: l) Is GF)
    dsimp only [localCtx, crashStart]
    isplitl [Hc1 Hc2]
    · isplitl [Hc1] <;> iassumption
    · isplitl [Hs1] <;> iassumption

end Exts

/-- How the ghost state of the extensions of the program survives a crash: one
`ExtCrashInterp` for each. -/
class GooseCrashInterp [GooseExts] [GooseSemantics] [GooseInterp] where
  crashInterps : Exts.CrashInterp exts GooseSemantics.sems GooseInterp.interps

section exts
variable [GooseExts] [GooseSemantics] [GooseInterp] [GooseCrashInterp] {GF : BundledGFunctors}

/-- The extensions' resources for the recovery procedure, relating the local
ghost state `L` of the crashed generation and `L'` of the new one. -/
abbrev extsCrashStart (L L' : GooseLocalGS GF) : IProp GF :=
  Exts.crashStart exts GooseSemantics.sems GooseInterp.interps GooseCrashInterp.crashInterps
    L.gooseExtsLocalGS L'.gooseExtsLocalGS

end exts

section crash
variable [GooseExts] [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp]
variable {GF : BundledGFunctors}

/-! ## The crash -/

/-- The crash of a generation, in the ghost state: the state interpretation of
the generation with local ghost state `L`, at a state that crashes to `σ'`,
gives way to that of a new generation `L'` at the crashed configuration (step
fuel kept, thread fuel `T - 2`), with the old generation's `crashed`, the
extensions' `crashStart`, the new package state and the new main thread's
token. -/
theorem goose_crash_step [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF]
    [L : GooseLocalGS GF] (T : Nat) (hT : 1 < T) {σ σ' : state} (hc : Crash σ σ')
    (g : GlobalState) (f : Fuel) (κs : List Observation) :
    gooseBstateInterp (((σ, g), f) : BcfgState) κs ⊢ |==> ∃ L' : GooseLocalGS GF,
      ⌜L'.goose_go_local_context = L.goose_go_local_context⌝ ∗
      ⌜@ThreadGS.threadBound GF L'.goose_threadGS = T⌝ ∗
      gooseBstateInterp (L := L') (((σ', g), ⟨f.steps, T - 2⟩) : BcfgState) κs ∗
      crashed (hC := L.goose_crashGS) ∗ extsCrashStart L L' ∗
      ownGoState (hG := L'.goose_go_stateGS) ∅ ∗ threadTok (hT := L'.goose_threadGS) := by
  unfold gooseBstateInterp gooseStateInterp
  iintro ⟨⟨-, Hext, -, %Hlctx, Hg, Hp⟩, Hr, -, Hnc⟩
  imod notCrashed_crash $$ Hnc with #Hcr
  imod na_heap_init (L := Loc) (V := val) tls σ'.heap with ⟨%hHeap, Hh⟩
  imod goState_init hPre.goose_preG_go_state ∅ with ⟨%γ, Hgs, Hgs'⟩
  imod Exts.local_crash exts _ _ GooseCrashInterp.crashInterps hPre.goosePreGExts
    L.gooseExtsLocalGS σ.world σ'.world hc.world $$ Hext with ⟨%hFL, Hext, Hcs⟩
  imod thread_init T hT with ⟨%γT, HT⟩
  imod crashToken_init with ⟨%γC, HC⟩
  have Hsplit := (threadToks_add (hT := ⟨γT, T, hT⟩) (T - 2) 1).1
  rw [show T - 2 + 1 = T - 1 by omega] at Hsplit
  icases Hsplit $$ HT with ⟨Hfuel, Htok⟩
  imodintro
  iexists (⟨hFL, L.goose_go_local_context, hHeap,
    goStateGSUpdatePre GF hPre.goose_preG_go_state γ, ⟨γT, T, hT⟩, ⟨γC⟩⟩ : GooseLocalGS GF)
  isplitr
  · ipureintro; rfl
  isplitr
  · ipureintro; rfl
  rw [hc.packageState]
  unfold threadFuel
  iframe
  isplitl []
  · ipureintro; rw [hc.goLctx, Hlctx]
  iexact Hcr

/-! ## Executions with crashes in the ghost state -/

omit [GooseCrashInterp] in
theorem steps_sum_zero (ns n : Nat) : steps_sum (fun _ => 0) ns n = n := by
  induction n generalizing ns with
  | zero => rfl
  | succ n ih => simp only [steps_sum, ih]; omega

omit [GooseInterp] [GooseSemantics] [GoGlobalContext] [GooseCrashInterp] in
/-- A fancy update in front of steps that end in a fancy update is absorbed. -/
theorem fupd_step_fupdN_absorb {Hinv : InvGS_gen .hasLC GF} (m : Nat) (P : IProp GF) :
    (|={∅}=> |={∅}▷=>^[m] |={∅,⊤}=> P) ⊢ |={∅}▷=>^[m] |={∅,⊤}=> P := by
  cases m with
  | zero => exact BIFUpdate.trans
  | succ m => exact BIFUpdate.trans

/-- `goose_irisGS` for the ghost state `⟨G, L⟩`. -/
abbrev gooseIrisGS (G : GooseGlobalGS .hasLC GF) (L : GooseLocalGS GF) :
    IrisGS_gen .hasLC Expr GF :=
  goose_irisGS

/-- The thread pool `es` with postconditions `Φs`, under the ghost state `⟨G, L⟩`. -/
abbrev gooseWptp [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF] (es : List Expr)
    (Φs : List (val → IProp GF)) : IProp GF :=
  wptp (iG := goose_irisGS) Stuckness.NotStuck es Φs

/-- The postcondition of a forked thread (`forkPost`). -/
abbrev forkPosts (n : Nat) : List (val → IProp GF) :=
  List.replicate n (fun v => iprop(⌜v.isPanic = false⌝))

/-- One generation of `n` steps, in the ghost state: iris-lean's
`wptp_preservation` for the GooseLang ghost state `⟨G, L⟩`. -/
theorem goose_wptp_preservation [G : GooseGlobalGS .hasLC GF] [L : GooseLocalGS GF] {n : Nat}
    {ρ ρ' : List Expr × BcfgState} {κs : List Observation} (H : Language.NSteps n ρ κs ρ')
    (κs' : List Observation) (Φs : List (val → IProp GF)) :
    ⊢ gooseBstateInterp ρ.2 (κs ++ κs') -∗ £ n -∗ gooseWptp ρ.1 Φs ={⊤,∅}=∗
      |={∅}▷=>^[n] |={∅,⊤}=> ∃ nt', gooseBstateInterp ρ'.2 κs' ∗
        gooseWptp ρ'.1 (Φs ++ forkPosts nt') := by
  have := wptp_preservation (iG := goose_irisGS) Stuckness.NotStuck n ρ.1 ρ'.1 κs κs' ρ.2 ρ'.2 0
    Φs 0 H
  rw [show steps_sum goose_irisGS.numLatersPerStep 0 n = n from steps_sum_zero 0 n] at this
  exact this

/-- Executions with crashes, in the ghost state: from the state interpretation,
the credits and the WPs of the thread pool (the main thread's postcondition
`Φ`) of a generation `L`, and its crash frame `Ψ L`, the configuration reached
by `n` steps with crashes has the state interpretation and the WPs of a
generation `L'` (the main thread's postcondition `Φ` if there was no crash, the
recovery's `φr` otherwise). The recovery premise `Hrec` is `goose_crash_adequacy`'s
for the fixed global ghost state `G`. -/
theorem goose_crash_preservation [hPre : GooseGpreS GF] [G : GooseGlobalGS .hasLC GF]
    (r : Expr) (T : Nat) (lctx : GoLocalContext) (φr : val → Prop)
    (Ψ : GooseLocalGS GF → IProp GF)
    (Hrec : ∀ (L L' : GooseLocalGS GF),
      @ThreadGS.threadBound GF L'.goose_threadGS = T →
      L'.goose_go_local_context = lctx →
      ⊢ Ψ L -∗ crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ threadTok (hT := L'.goose_threadGS) ={⊤}=∗
        WP r @ Stuckness.NotStuck; ⊤ {{ v, ⌜φr v⌝ }} ∗ Ψ L')
    {n : Nat} {ρ ρ' : List Expr × BcfgState} {κs : List Observation} {b : Bool}
    (H : BoundedCrashNsteps r T n ρ κs ρ' b) :
    ∀ (L : GooseLocalGS GF) (κs' : List Observation) (Φ : val → IProp GF) (k : Nat),
      @ThreadGS.threadBound GF L.goose_threadGS = T → L.goose_go_local_context = lctx →
      ⊢ gooseBstateInterp ρ.2 (κs ++ κs') -∗ £ n -∗ gooseWptp ρ.1 (Φ :: forkPosts k) -∗ Ψ L
        ={⊤,∅}=∗ |={∅}▷=>^[n] |={∅,⊤}=> ∃ (L' : GooseLocalGS GF) (k' : Nat),
          gooseBstateInterp (L := L') ρ'.2 κs' ∗
          gooseWptp (L := L') ρ'.1 ((bif b then fun v => iprop(⌜φr v⌝) else Φ) :: forkPosts k') := by
  induction H with
  | done H =>
    intro L κs' Φ k _ _
    iintro Hσ Hcred Hwp _
    imod goose_wptp_preservation H κs' _ $$ Hσ Hcred Hwp with H
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%nt', Hσ, Hwp⟩
    imodintro
    iexists L, k + nt'
    iframe Hσ
    simp only [forkPosts, List.cons_append, List.replicate_append_replicate, Bool.cond_false]
    iexact Hwp
  | @crash n m ρ κs t σ g f σ' κs₂ ρ' b H₁ hc _ ih =>
    intro L κs' Φ k HT Hlctx
    have hT : 1 < T := HT ▸ L.goose_threadGS.threadBound_gt
    iintro Hσ Hcred Hwp HΨ
    rw [List.append_assoc]
    icases lc_split.1 $$ Hcred with ⟨Hcred₁, Hcred₂⟩
    imod goose_wptp_preservation H₁ (κs₂ ++ κs') _ $$ Hσ Hcred₁ Hwp with H
    imodintro
    rw [(step_fupdN_add (n := n) (m := m)).to_eq]
    iapply step_fupdN_wand $$ H
    iintro H
    iapply fupd_step_fupdN_absorb
    imod H with ⟨%nt', Hσ, -⟩
    imod goose_crash_step (L := L) T hT hc g f (κs₂ ++ κs') $$ Hσ
      with ⟨%L', %HL'lctx, %HL'T, Hσ, Hcr, Hcs, Hgs, Htok⟩
    imod Hrec L L' HL'T (by rw [HL'lctx, Hlctx]) $$ HΨ Hcr Hcs Hgs Htok with ⟨Hwp, HΨ⟩
    imod ih L' κs' (fun v => iprop(⌜φr v⌝)) 0 HL'T (by rw [HL'lctx, Hlctx]) $$ Hσ Hcred₂
      [Hwp] HΨ with H
    · simp only [forkPosts, List.replicate_zero]
      iapply BigSepL2.bigSepL2_singleton.2
      iexact Hwp
    imodintro
    iapply step_fupdN_wand $$ H
    iintro H
    imod H with ⟨%L'', %k', Hσ, Hwp⟩
    imodintro
    iexists L'', k'
    iframe Hσ
    simp only [Bool.cond_self, Bool.cond_true]
    iexact Hwp

omit [GooseSemantics] [GoGlobalContext] [GooseCrashInterp] in
/-- Every thread of `l` that is a value satisfies `P`, from their postconditions. -/
theorem bigSepL_toVal_pure (l : List Expr) (P : val → Prop) :
    ([∗list] e ∈ l, (toVal e).elim iprop(True) (fun v => iprop(⌜P v⌝))) ⊢@{IProp GF}
      ⌜∀ v, Val v ∈ l → P v⌝ := by
  induction l with
  | nil => iintro _; ipureintro; simp
  | cons e l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨He, Hl⟩
    icases ih $$ Hl with %Hl
    cases e with
    | Val v =>
      simp only [toVal, Option.elim]
      icases He with %He
      ipureintro
      intro w hw
      rcases List.mem_cons.1 hw with h | h
      · cases h; exact He
      · exact Hl w h
    | _ =>
      ipureintro
      intro w hw
      rcases List.mem_cons.1 hw with h | h
      · cases h
      · exact Hl w h

/-! ## Adequacy -/

/-- Crash adequacy of the bounded language: under the hypotheses of
`goose_crash_adequacy`, in every execution with crashes of the bounded
semantics started with step fuel `N - 1` and thread fuel `T - 2`, the main
thread's final value satisfies `φ` (no crash) or `φr` (crashed), every thread is
a value or can step, and no thread is a panic. -/
theorem goose_crash_adequacy_blang [hPre : GooseGpreS GF] (N T : Nat) (hN : 0 < N) (hT : 1 < T)
    (e r : Expr) (σ : state) (g : GlobalState) (φ φr : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p)) (hφr : ∀ p, ¬ φr (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ψ : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG)
    (Hrec : ∀ (hG : HeapGS .hasLC GF) [hG' : HeapGS .hasLC GF],
      hG'.goose_globalGS = hG.goose_globalGS →
      receiptBound GF = N →
      threadBound GF = T →
      hG'.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ Ψ hG -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        extsCrashStart hG.goose_localGS hG'.goose_localGS -∗
        ownGoState ∅ -∗ threadTok ={⊤}=∗
        WP r @ Stuckness.NotStuck; ⊤ {{ v, ⌜φr v⌝ }} ∗ Ψ hG')
    {n : Nat} {κs : List Observation} {t2 : List Expr} {σ2 : BcfgState} {b : Bool}
    (Hsteps : BoundedCrashNsteps r T n ([e], (((σ, g), ⟨N - 1, T - 2⟩) : BcfgState)) κs
      (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → (bif b then φr else φ) v) ∧
      (∀ e2, e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)) ∧
      (∀ v, Val v ∈ t2 → v.isPanic = false) := by
  apply pure_soundness (PROP := IProp GF)
  apply laterN_soundness (n := n + 1)
  rw [(laterN_succ_right _).to_eq]
  refine Entails.trans ?_ (laterN_mono _ except0_into_later)
  apply fupd_finally_soundness .hasLC n ⊤
  iintro %Hinv Hf
  imod goose_init (Hinv := Hinv) N T hN hT σ g κs Hinitg Hinit
    (fun (hG : HeapGS .hasLC GF) => iprop(
      ⌜receiptBound GF = N ∧ threadBound GF = T ∧
        hG.goose_localGS.goose_go_local_context = σ.goState.goLctx⌝ ∗
      WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG))
    (@fun hG HinvEq HN HT Hlctx => by
      subst HinvEq
      iintro Hg Hl Hgs Htok
      imod Hwp (hG := hG) HN HT Hlctx $$ Hg Hl Hgs Htok with ⟨Hwp, HΨ⟩
      imodintro
      iframe
      ipureintro; exact ⟨HN, HT, Hlctx⟩)
    with ⟨%hG, %HinvEq, Hσ, %⟨HN, HT, Hlctx⟩, Hwp, HΨ⟩
  obtain ⟨⟨Ginv, Gall, Gproph, Gext, Grcpt⟩, L⟩ := hG
  cases HinvEq
  let G : GooseGlobalGS .hasLC GF := ⟨Ginv, Gall, Gproph, Gext, Grcpt⟩
  have Hrec' : ∀ (L L' : GooseLocalGS GF),
      @ThreadGS.threadBound GF L'.goose_threadGS = T →
      L'.goose_go_local_context = σ.goState.goLctx →
      ⊢ Ψ ⟨G, L⟩ -∗ crashed (hC := L.goose_crashGS) -∗ extsCrashStart L L' -∗
        ownGoState (hG := L'.goose_go_stateGS) ∅ -∗ threadTok (hT := L'.goose_threadGS) ={⊤}=∗
        WP r @ Stuckness.NotStuck; ⊤ {{ v, ⌜φr v⌝ }} ∗ Ψ ⟨G, L'⟩ :=
    fun L L' HT' Hlctx' => Hrec (hG' := ⟨G, L'⟩) ⟨G, L⟩ rfl HN HT' Hlctx'
  have Hpres := goose_crash_preservation (G := G) r T σ.goState.goLctx φr (fun L => Ψ ⟨G, L⟩)
    Hrec' Hsteps L [] (fun v => iprop(⌜φ v⌝)) 0 HT Hlctx
  rw [List.append_nil] at Hpres
  imod Hpres $$ Hσ Hf [Hwp] HΨ with H
  · simp only [gooseWptp, forkPosts, List.replicate_zero]
    iapply BigSepL2.bigSepL2_singleton.2
    iexact Hwp
  iapply step_fupdN_fupd_finally
  iapply step_fupdN_wand $$ H
  iintro >⟨%L', %k', Hσ, Ht⟩
  iapply fupd_finally_keep iprop(⌜∀ e2, e2 ∈ t2 → PrimStep.NotStuck (e2, σ2)⌝)
  isplit
  · iintro %e %Hin
    obtain ⟨i, He⟩ := List.getElem?_of_mem Hin
    icases BigSepL2.bigSepL2_lookup_left $$ Ht with ⟨%Φ', _, He⟩; exact He
    imod wp_not_stuck (iG := gooseIrisGS G L') (κs := []) (nt := 0) (ns := 0) $$ Hσ He with %_
    itrivial
  iintro %Hns
  imod wptp_postconditions (iG := gooseIrisGS G L') $$ Ht with Ht
  icases BigSepL2.bigSepL2_cons_inv_right $$ Ht with ⟨%e0, %t2', %Heq, He0, Ht2'⟩
  subst Heq
  icases BigSepL2.bigSepL2_length $$ Ht2' with %Hlen
  rw [List.length_replicate] at Hlen
  subst Hlen
  icases BigSepL2.bigSepL2_replicate_right $$ Ht2' with Ht2'
  icases bigSepL_toVal_pure t2' (fun v => v.isPanic = false) $$ Ht2' with %Hforks
  suffices Hm : (toVal e0).elim iprop(True)
      (bif b then fun v => iprop(⌜φr v⌝) else fun v => iprop(⌜φ v⌝)) ⊢@{IProp GF}
      ⌜∀ v, e0 = Val v → (bif b then φr else φ) v⌝ by
    icases Hm $$ He0 with %Hm
    ipureintro
    refine ⟨fun v t2'' h => ?_, Hns, fun v hv => ?_⟩
    · cases h; exact Hm v rfl
    · rcases List.mem_cons.1 hv with h | h
      · have := Hm v h.symm
        cases b <;> cases v <;> first | rfl | exact absurd this (hφ _) | exact absurd this (hφr _)
      · exact Hforks v h
  cases e0 <;> cases b <;> simp only [toVal, Option.elim, Bool.cond_true, Bool.cond_false] <;>
    first
    | (iintro %H; ipureintro; rintro v ⟨⟩; exact H)
    | (iintro _; ipureintro; rintro v ⟨⟩)

/-- Crash adequacy of GooseLang, for the real semantics, with a recovery
procedure `r` that may differ from the program `e` (for a single boot program,
see `goose_crash_adequacy`): for any bounds `N` and `T`, if

* `Hwp`: the WP of the program `e` is proved, for receipt bound `N` and thread
  bound `T`, as for `goose_adequacy`, together with the crash frame `Ψ` of the
  first generation;
* `Hrec`: for a generation `hG` that crashed and the next one `hG'` (the same
  global ghost state, a new local one, with the same bounds), the WP of the
  recovery procedure `r` is proved from the crash frame of `hG`, the evidence
  `crashed` that `hG` has crashed, the extensions' `crashStart` resources, the
  package state of a restarted program (no package initialized) and the new
  main thread's token, together with the crash frame of `hG'`;

with postconditions that exclude panics (`hφ`, `hφr`), then in every real
execution with crashes of `e` with recovery `r` (`RealCrashNsteps`) of fewer
than `N` steps in all, from a configuration with the main thread only, along
which fewer than `T` threads are live (`RealCrashThreadsBelow`):
* if the main thread has terminated with `v`, then `φ v` if there was no
  crash, `φr v` if there was;
* every thread is a value or can take a step;
* no thread has an unrecovered panic. -/
theorem goose_crash_adequacy_recovery [hPre : GooseGpreS GF] (N T : Nat)
    (e r : Expr) (σ : state) (g : GlobalState) (φ φr : val → Prop)
    (hφ : ∀ p, ¬ φ (PanicV p)) (hφr : ∀ p, ¬ φr (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ψ : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF],
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ extsGlobalStart (GF := GF) g.globalWorld -∗
        extsLocalStart (GF := GF) σ.world -∗
        ownGoState σ.goState.packageState -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG)
    (Hrec : ∀ (hG : HeapGS .hasLC GF) [hG' : HeapGS .hasLC GF],
      hG'.goose_globalGS = hG.goose_globalGS →
      receiptBound GF = N →
      threadBound GF = T →
      hG'.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ Ψ hG -∗ crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        extsCrashStart hG.goose_localGS hG'.goose_localGS -∗
        ownGoState ∅ -∗ threadTok ={⊤}=∗
        WP r @ Stuckness.NotStuck; ⊤ {{ v, ⌜φr v⌝ }} ∗ Ψ hG')
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps r n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow r T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → if b then φr v else φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have hT : 1 < T := by have := Hlive.start; simp only at this; omega
  obtain ⟨c, t, Hb⟩ := bounded_crash_nsteps_of_real Hsteps (N - 1) (by omega) T (T - 2) Hlive
    (by simp only; omega)
  have H := goose_crash_adequacy_blang N T (by omega) hT e r σ g φ φr hφ hφr Hinitg Hinit Ψ
    Hwp Hrec Hb
  refine ⟨fun v t2' h => ?_, fun e2 he2 => realNotStuck_of_bounded (H.2.1 e2 he2), ?_⟩
  · have := H.1 v t2' h; cases b <;> exact this
  intro e2 He2 Hu
  obtain ⟨p, Hp⟩ := unrecoveredPanic_steps Hu
  obtain ⟨t₁, t₂, rfl⟩ := List.append_of_mem He2
  obtain ⟨m, κs', Hm⟩ := (Language.erasedStep_nSteps _ _).mp (Hp [] t₁ t₂ (σ2, ⟨c, t⟩))
  have := (goose_crash_adequacy_blang N T (by omega) hT e r σ g φ φr hφ hφr Hinitg Hinit Ψ
    Hwp Hrec (Hb.append Hm)).2.2 (PanicV p) (by simp)
  simp [val.isPanic] at this

/-- What a boot of the node gives the boot program, in the generation `hG`
(the precondition of every boot, `goose_crash_adequacy`): on the first boot
(`prev = none`), the extensions' start resources and the initial package state;
on the boot after the crash of the generation with local ghost state `L`
(`prev = some L`), that generation's crash frame `Ψ`, its `crashed`, the
extensions' `crashStart` resources relating it to `hG`, and the package state
of a restarted program (no package initialized). -/
def bootStart (Ψ : HeapGS .hasLC GF → IProp GF) (σ : state) (g : GlobalState)
    [hG : HeapGS .hasLC GF] : Option (GooseLocalGS GF) → IProp GF
  | none => iprop(extsGlobalStart (G := hG.goose_globalGS) g.globalWorld ∗
      extsLocalStart (L := hG.goose_localGS) σ.world ∗
      ownGoState (hG := hG.goose_localGS.goose_go_stateGS) σ.goState.packageState)
  | some L => iprop(Ψ ⟨hG.goose_globalGS, L⟩ ∗ crashed (hC := L.goose_crashGS) ∗
      extsCrashStart L hG.goose_localGS ∗ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅)

/-- Crash adequacy of GooseLang for a single boot program `e`, which runs at the
start and again after every crash, for the real semantics: for any bounds `N`
and `T`, if the WP of `e` is proved, for receipt bound `N` and thread bound `T`,
from what any boot gives it (`bootStart Ψ σ g prev`, for the first boot and for
the boot after any crash) and the main thread's token, together with the crash
frame `Ψ` of its own generation, with a postcondition `φ` that excludes panics,
then in every real execution with crashes of `e` (`RealCrashNsteps e`) of fewer
than `N` steps in all, from a configuration with the main thread only, along
which fewer than `T` threads are live (`RealCrashThreadsBelow`):
* if the main thread has terminated with `v`, then `φ v`;
* every thread is a value or can take a step;
* no thread has an unrecovered panic. -/
theorem goose_crash_adequacy [hPre : GooseGpreS GF] (N T : Nat)
    (e : Expr) (σ : state) (g : GlobalState) (φ : val → Prop) (hφ : ∀ p, ¬ φ (PanicV p))
    (Hinitg : extsInitgP g.globalWorld) (Hinit : extsInitP σ.world g.globalWorld)
    (Ψ : HeapGS .hasLC GF → IProp GF)
    (Hwp : ∀ [hG : HeapGS .hasLC GF] (prev : Option (GooseLocalGS GF)),
      receiptBound GF = N →
      threadBound GF = T →
      hG.goose_localGS.goose_go_local_context = σ.goState.goLctx →
      ⊢ bootStart Ψ σ g prev -∗ threadTok ={⊤}=∗
        WP e @ Stuckness.NotStuck; ⊤ {{ v, ⌜φ v⌝ }} ∗ Ψ hG)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps e n ([e], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow e T n ([e], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → φ v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  have H := goose_crash_adequacy_recovery N T e e σ g φ φ hφ hφ Hinitg Hinit Ψ ?_ ?_ n κs t2 σ2 b
    Hsteps Hbound Hthreads Hlive
  · exact ⟨fun v t2' h => by have := H.1 v t2' h; cases b <;> exact this, H.2⟩
  · intro hG HN HT Hlctx
    iintro Hg Hl Hgs Htok
    iapply Hwp none HN HT Hlctx $$ [Hg Hl Hgs] Htok
    dsimp only [bootStart]
    iframe
  · intro hG hG' HG HN HT Hlctx
    obtain ⟨G, L⟩ := hG
    obtain ⟨G', L'⟩ := hG'
    cases HG
    iintro HΨ Hcr Hcs Hgs Htok
    iapply Hwp (hG := ⟨G, L'⟩) (some L) HN HT Hlctx $$ [HΨ Hcr Hcs Hgs] Htok
    dsimp only [bootStart]
    iframe

end crash

end Perennial
