/-
A crash obligation with a later credit (regression test of the crash obligations of
`goose_crash_adequacy`, `GooseLang/CrashAdequacy.lean`).

A toy extension, `epochExt`, keeps the node's epoch: its local state counts the node's crashes
(`crash s s' := s' = s + 1`), and its operation `Epoch` returns it. Its ghost state is per
generation: a crash hands the restart nothing (`crashStart := True`), and the interpretation of
epoch `s` is the persistent witness (`epochWit`) of a ghost variable `γ` at `s`, determined by
the state. `Epoch` hands out the witness of the epoch it returns, and returns the epoch of any
witness.

The node runs `boot`, `(Epoch(), Epoch())`, at the start and after every crash: it returns a pair
of equal epochs, which the witness proves. Besides, the node keeps a value that is not timeless
(a saved proposition, `bootPre`) from each generation to the next, in the generation's crash
invariant `inv genN (savedPropOwn γ 1 True ∨ crashed ∗ token γt)` (the pattern of state shared
with the generation's threads, `NotCrashedChanTest`; here no thread uses it). The crash
obligation opens the invariant, gets the value under a later, and strips it with the crash's
later credit to hand it to the next generation.

* `wp_Epoch_wit`, `wp_Epoch`: the specs of `Epoch`.
* `gen_safety`: `goose_crash_adequacy` for `boot`, for every execution with crashes.
-/
module

public import Perennial.GooseLang.CrashAdequacy
public import Perennial.Golang.Theory.Auto
public import Perennial.Ghost.DGhostVar
public import Perennial.Ghost.SavedProp
public import Perennial.Ghost.Token

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

namespace GenStartTest

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## The extension -/

/-- The node's epoch. -/
@[reducible] def epochExt : GooseExt where
  name := "epoch"
  Val := Empty
  LocalState := Nat
  GlobalState := Unit

section step
variable [GooseExts] [GoGlobalContext]

/-- `Epoch` returns the epoch. -/
inductive EpochStep : String → val → GMap Loc (NonAtomic val) → Nat → Unit → Expr →
    GMap Loc (NonAtomic val) → Nat → Unit → Prop
  | epoch (h : GMap Loc (NonAtomic val)) (n : Nat) :
      EpochStep "Epoch" #() h n () (Val #(BitVec.ofNat 64 n)) h n ()

end step

/-- A crash increments the epoch. -/
instance epoch_semantics : ExtSemantics epochExt where
  step := EpochStep
  crash s s' := s' = s + 1

/-! ## Its ghost state -/

/-- The ghost state of a generation's epoch: a ghost variable. -/
structure EpochGS (GF : BundledGFunctors) where
  allG : AllG GF
  γ : GName

section ghost
variable {GF : BundledGFunctors}

/-- The epoch's ghost variable, persistent: the witness that the epoch is `n`. -/
def epochWit (hL : EpochGS GF) (n : Nat) : IProp GF :=
  @dghostVar GF hL.allG Nat _ hL.γ .discard n

instance epochWit_persistent (hL : EpochGS GF) (n : Nat) : Persistent (epochWit hL n) := by
  unfold epochWit; letI := hL.allG; infer_instance

/-- A new generation's epoch. -/
theorem epoch_alloc (hPre : AllG GF) (n : Nat) :
    ⊢@{IProp GF} |==> ∃ hL : EpochGS GF, epochWit hL n := by
  letI := hPre
  imod (dghostVar_alloc (GF := GF) n) with ⟨%γ, H⟩
  imod dghostVar_persist γ 1 n $$ H with H
  imodintro
  iexists (⟨hPre, γ⟩ : EpochGS GF)
  unfold epochWit
  iexact H

/-- A witness of `n` agrees with the interpretation of `m`. -/
theorem epoch_agree (hL : EpochGS GF) (m n : Nat) :
    ⊢ epochWit hL m -∗ epochWit hL n -∗ ⌜m = n⌝ := by
  letI := hL.allG
  unfold epochWit
  iintro H1 H2
  iapply dghostVar_agree $$ H1 H2

end ghost

/-- The interpretation of epoch `s`: the witness of its ghost variable. The restart is handed
nothing. -/
instance epoch_interp : ExtInterp epochExt where
  LocalGS := EpochGS
  GlobalGS _ := Unit
  localCtx hL s := epochWit hL s
  globalCtx _ _ := iprop(True)
  PreG := AllG
  initgP _ := True
  initP _ _ := True
  globalStart _ _ := iprop(True)
  localStart _ _ := iprop(True)
  global_init _ _ _ _ := by
    iapply bupd_intro; iexists (); isplitl [] <;> itrivial
  local_init GF hPre s _ _ := by
    imod epoch_alloc (GF := GF) hPre s with ⟨%hL, H⟩
    imodintro
    iexists hL
    isplitl [H]
    · iexact H
    · itrivial

theorem epoch_ctx {GF : BundledGFunctors} (hL : EpochGS GF) (s : Nat) :
    ExtInterp.localCtx (E := epochExt) hL s ⊣⊢ epochWit hL s := .rfl

/-- At a crash, the epoch's ghost variable is allocated anew, at the new epoch. -/
instance epoch_crash_interp : ExtCrashInterp epochExt where
  crashStart _ _ := iprop(True)
  local_crash GF hPre _ _ σ' _ := by
    iintro _
    imod epoch_alloc (GF := GF) hPre σ' with ⟨%hL, H⟩
    imodintro
    iexists hL
    isplitl [H]
    · iapply (epoch_ctx _ _).2; iexact H
    · itrivial

/-! ## The spec of `Epoch` -/

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt epochExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {s : Stuckness} {E : CoPset}

/-- The witness that the generation's epoch is `n`. -/
abbrev epochIs (n : Nat) : IProp GF := epochWit (extLocalGS epochExt (L := L)) n

/-- `Epoch` returns the epoch, and its witness. -/
theorem wp_Epoch_wit :
    {{ True }} (ExternalOp epochExt.name "Epoch" (Val #())) @ s; E
    {{ (n : Nat), RET #(BitVec.ofNat 64 n); epochIs (L := L) n }} := by
  iintro %Φ _ HΦ
  iapply wp_extStep "Epoch" #() Φ (by simp)
  iintro %h %m %g Hh Hl Hg
  icases (epoch_ctx _ _).1 $$ Hl with #Hm
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, m, (), EpochStep.epoch h m⟩
  inext
  iintro %e' %h' %m' %g' %Hst _
  cases (show EpochStep _ _ _ _ _ _ _ _ _ from Hst)
  imod Hclose
  imodintro
  iframe Hh Hg
  isplitl []
  · iapply (epoch_ctx _ _).2; iexact Hm
  iapply wp_value'
  iapply HΦ
  iexact Hm

/-- With the witness that the epoch is `n`, `Epoch` returns `n`. -/
theorem wp_Epoch (n : Nat) :
    {{ epochIs (L := L) n }} (ExternalOp epochExt.name "Epoch" (Val #())) @ s; E
    {{ RET #(BitVec.ofNat 64 n); True }} := by
  iintro %Φ #Hw HΦ
  iapply wp_extStep "Epoch" #() Φ (by simp)
  iintro %h %m %g Hh Hl Hg
  icases (epoch_ctx _ _).1 $$ Hl with #Hm
  ihave %Heq := epoch_agree _ m n $$ Hm Hw
  subst Heq
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro; exact ⟨_, h, m, (), EpochStep.epoch h m⟩
  inext
  iintro %e' %h' %m' %g' %Hst _
  cases (show EpochStep _ _ _ _ _ _ _ _ _ from Hst)
  imod Hclose
  imodintro
  iframe Hh Hg
  isplitl []
  · iapply (epoch_ctx _ _).2; iexact Hm
  iapply wp_value'
  iapply HΦ
  itrivial

end spec

/-! ## The program -/

@[reducible] def epochExts : GooseExts := ⟨[epochExt]⟩

attribute [local instance] epochExts

@[reducible] def epochSemantics : GooseSemantics := ⟨(epoch_semantics, ⟨⟩)⟩

@[reducible] def epochInterp : GooseInterp := ⟨(epoch_interp, ⟨⟩)⟩

attribute [local instance] epochSemantics epochInterp

@[reducible] def epochCrashInterp : GooseCrashInterp := ⟨(epoch_crash_interp, ⟨⟩)⟩

attribute [local instance] epochCrashInterp

theorem epochExts_hasEpoch : HasExt epochExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

attribute [local instance] epochExts_hasEpoch

/-- The boot program: the epoch, twice. -/
def boot [GoGlobalContext] : Expr :=
  Pair (ExternalOp epochExt.name "Epoch" (Val #())) (ExternalOp epochExt.name "Epoch" (Val #()))

/-! ## Crash safety -/

abbrev genN : Namespace := nroot.@"gen"

section adequacy
variable {GF : BundledGFunctors}

/-- The boot program's precondition: a value handed from each generation to the next, which
is not timeless (a saved proposition). -/
def bootPre [G : GooseGlobalGS .hasLC GF] (_L : GooseLocalGS GF) : IProp GF :=
  iprop(∃ γ : GName, savedPropOwn γ (.own 1) iprop(True))

/-- The boot program returns a pair of equal values. -/
def bootPost (v : val) : Prop := ∃ x, v = PairV x x

theorem bootPost_not_panic (p : val) : ¬ bootPost (PanicV p) := by
  rintro ⟨x, h⟩; cases h

set_option maxHeartbeats 400000 in
/-- **A generation**: from its precondition, the WP of `boot` (whose first `Epoch` hands out
the witness for the second) and the crash invariant, which the crash obligation empties with
the crash's later credit. -/
theorem wp_gen [GoGlobalContext] [hG : HeapGS .hasLC GF] :
    ⊢ bootPre (GF := GF) hG.goose_localGS ={⊤}=∗
      WP boot @ Stuckness.NotStuck; ⊤ {{ v, ⌜bootPost v⌝ }} ∗
      ∀ L' : GooseLocalGS GF, crashed (hC := hG.goose_localGS.goose_crashGS) -∗
        extsCrashStart hG.goose_localGS L' -∗ ownGoState (hG := L'.goose_go_stateGS) ∅ -∗
        £ 1 ={⊤}=∗ bootPre L' := by
  unfold bootPre
  iintro ⟨%γ, Hv⟩
  -- the crash invariant
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod inv_alloc genN ⊤ iprop(savedPropOwn γ (.own 1) iprop(True) ∨
      crashed (hC := hG.goose_localGS.goose_crashGS) ∗ token γt) $$ [Hv] with #Hinv
  · inext; ileft; iexact Hv
  imodintro
  isplitl []
  · -- the program: the second call returns the epoch of the first one's witness
    unfold boot
    wp_apply wp_Epoch_wit $$ []
    · itrivial
    iintro %n #Hw
    wp_apply wp_Epoch n $$ [Hw]
    · iexact Hw
    iintro _
    wp_auto
    ipureintro
    exact ⟨_, rfl⟩
  · -- the crash obligation: `token γt` rules out the crash side, and the credit strips the
    -- later off the value
    iintro %L' #Hcr _ _ Hlc
    imod inv_acc (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨H, Hclose⟩
    icases H with (Hv | > ⟨_, Ht2⟩)
    · imod lc_fupd_elim_later $$ Hlc Hv with Hv
      imod Hclose $$ [Ht] with -
      · inext
        iright
        iframe Ht
        iexact Hcr
      imodintro
      iexists γ
      iexact Hv
    · iexfalso
      iapply token_exclusive $$ Ht Ht2

/-- `gen_safety` for executions of fewer than `N` steps along which fewer than `T` threads are
live: `goose_crash_adequacy` for `boot`, with `bootPre`. -/
theorem gen_safety_bounded [GoGlobalContext] [hPre : GooseGpreS GF]
    (N T : Nat) (σ : state) (g : GlobalState)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps boot n ([boot], ((σ, g) : CfgState)) κs (t2, σ2) b)
    (Hbound : n < N) (Hthreads : σ.threads = 1)
    (Hlive : RealCrashThreadsBelow boot T n ([boot], ((σ, g) : CfgState))) :
    (∀ v t2', t2 = Val v :: t2' → bootPost v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) := by
  refine goose_crash_adequacy (GF := GF) N T boot σ g bootPost bootPost_not_panic
    ⟨trivial, trivial⟩ ⟨trivial, trivial⟩ (fun L => bootPre L) ?_ ?_
    n κs t2 σ2 b Hsteps Hbound Hthreads Hlive
  · -- the first generation: a new value
    intro hG _ _ _
    iintro _ _ _
    imod saved_prop_alloc (GF := GF) iprop(True) (.own 1) DFrac.valid_own_one with ⟨%γ, Hv⟩
    imodintro
    unfold bootPre
    iexists γ
    iexact Hv
  · -- every generation: `wp_gen`
    intro hG _ _ _
    iintro HP _
    iapply wp_gen $$ HP

/-- **Crash safety** of the boot program: in every execution with crashes of `boot`, from a
state with the main thread only, the boot program returns a pair of equal values, no thread is
stuck and none has an unrecovered panic, however many times the node crashes.
(`gen_safety_bounded` with the step bound `n + 1` and the thread bound `n + 2`.) -/
theorem gen_safety [GoGlobalContext] [hPre : GooseGpreS GF] (σ : state) (g : GlobalState)
    (Hthreads : σ.threads = 1)
    (n : Nat) (κs : List Observation) (t2 : List Expr) (σ2 : CfgState) (b : Bool)
    (Hsteps : RealCrashNsteps boot n ([boot], ((σ, g) : CfgState)) κs (t2, σ2) b) :
    (∀ v t2', t2 = Val v :: t2' → bootPost v) ∧
      (∀ e2, e2 ∈ t2 → RealNotStuck e2 σ2) ∧
      (∀ e2, e2 ∈ t2 → ¬ UnrecoveredPanic e2) :=
  gen_safety_bounded (GF := GF) (n + 1) (n + 2) σ g n κs t2 σ2 b Hsteps (by omega) Hthreads
    (RealCrashThreadsBelow.of_single Hthreads)

end adequacy

end GenStartTest

end Perennial
