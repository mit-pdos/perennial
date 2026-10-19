/-
Shared definitions of the proofs of `sync.RWMutex`, with a logically atomic specification
over an abstract `rwmutex` state: the ghost names, the protocol invariant and its steps
(one per atomic operation of the code), `isRWMutex`, `ownRWMutex`, `ownRLockToken`, and
`init_RWMutex`. These are used qualified (`rwmutex.ownRWMutex`, namespace `sync.rwmutex`);
the guarded interface over them is in `RWMutexGuard`.
-/
module

public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.SemaDefs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option maxHeartbeats 400000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode

instance countable_rwmutex : Pos.Countable rwmutex :=
  .ofInjective (fun
      | .RLocked n => Pos.Countable.encode (some n)
      | .Locked => Pos.Countable.encode (none : Option Nat))
    (by rintro (a|_) (b|_) h <;> have h := Pos.encode_inj h <;> simp_all)

instance countable_wlock_state : Pos.Countable WlockState :=
  .ofInjective (fun
      | .NotLocked r => Pos.Countable.encode ((0 : Nat), r)
      | .SignalingReaders r => Pos.Countable.encode ((1 : Nat), r)
      | .WaitingForReaders => Pos.Countable.encode ((2 : Nat), W32 0)
      | .IsLocked => Pos.Countable.encode ((3 : Nat), W32 0))
    (by rintro (a|a|_|_) (b|b|_|_) h <;> have h := Pos.encode_inj h <;> simp_all)


namespace sync

/- These definitions are used qualified (`rwmutex.ownRWMutex`), since the
`rwmutex_guard` interface reuses the names for its fractional resources. -/
namespace rwmutex

/-- `rwmutexMaxReaders` as an `Int` (`sync.rwmutexMaxReaders` is the Go constant). -/
abbrev rwmutexMaxReadersZ : Int := 1073741824

/-- `rwmutexMaxReadersZ - 1` (sealed). -/
@[irreducible] def actualMaxReaders : Int := 1073741824 - 1
theorem actualMaxReaders_unseal : actualMaxReaders = 1073741824 - 1 := by
  with_unfolding_all rfl

structure RWMutexProtocolNames where
  readWaitGn : GName
  rlockOverflowGn : GName
  wlockGn : GName
  writerSemTokGn : GName
  stateGn : GName

-- (declared before the proofs: the kernel check of a `structure` waits for the
-- proofs elaborated asynchronously before it, which serialized this file)
structure RWMutexNames where
  protGn : RWMutexProtocolNames
  readerSemGn : GName
  writerSemGn : GName

section protocol
variable {GF : BundledGFunctors} [AllG GF]

abbrev rwInvReaders (state : rwmutex) (reader_sem pos_reader_count : w32) : IProp GF :=
  match state with
  | .RLocked num_readers =>
    iprop("%Hnum_readers_le" ∷ ⌜(num_readers : Int) + uint.Z reader_sem ≤ sint.Z pos_reader_count⌝)
  | _ => iprop("_" ∷ emp)

abbrev rwInvOutstanding (wl : WlockState) (outstanding_reader_wait : Nat) : IProp GF :=
  match wl with
  | .SignalingReaders _ | .WaitingForReaders => iprop("_" ∷ True)
  | _ => iprop("%Houtstanding_zero" ∷ ⌜outstanding_reader_wait = 0⌝)

abbrev rwInvWriter (γ : RWMutexProtocolNames) (wl : WlockState) : IProp GF :=
  match wl with
  | .WaitingForReaders => iprop("_" ∷ True)
  | _ => iprop("Hwriter_unused" ∷ ghostVar γ.writerSemTokGn 1 ())

abbrev rwInvMain (γ : RWMutexProtocolNames) (writer_sem reader_sem reader_wait : w32)
    (pos_reader_count : w32) (outstanding_reader_wait : Nat) (wl : WlockState)
    (state : rwmutex) : IProp GF :=
  match wl, state with
  | .NotLocked unnotified_readers, .RLocked num_readers =>
    iprop("%Hfast" ∷ ⌜reader_wait = W32 0 ∧ writer_sem = W32 0 ∧
      sint.Z pos_reader_count = (num_readers : Int) + sint.Z unnotified_readers + uint.Z reader_sem⌝)
  | .SignalingReaders remaining_readers, .RLocked num_readers =>
    iprop("%Hblocked_unsignaled" ∷ ⌜0 ≤ sint.Z remaining_readers ∧
      sint.Z remaining_readers < rwmutexMaxReadersZ ∧
      sint.Z reader_wait ≤ 0 ∧
      (outstanding_reader_wait : Int) + (num_readers : Int) + uint.Z reader_sem =
        sint.Z remaining_readers + sint.Z reader_wait ∧
      writer_sem = W32 0⌝)
  | .WaitingForReaders, .RLocked num_readers =>
    iprop("Hwriter" ∷ (ghostVar γ.writerSemTokGn 1 () ∨
        (ghostVar γ.writerSemTokGn (1 : Qp).half () ∗ ⌜writer_sem = W32 0 ∧ reader_wait = W32 0⌝)) ∗
      "%Hblocked" ∷ ⌜(outstanding_reader_wait : Int) + (num_readers : Int) + uint.Z reader_sem ≤
          sint.Z reader_wait ∧
        (writer_sem = W32 0 ∨ (writer_sem = W32 1 ∧ reader_wait = W32 0))⌝)
  | .IsLocked, .Locked =>
    iprop("%Hlocked" ∷ ⌜writer_sem = W32 0 ∧ reader_wait = W32 0 ∧ reader_sem = W32 0⌝)
  | _, _ => iprop(False)

abbrev RwReaderCountRel (wl : WlockState) (reader_count pos_reader_count : w32) : Prop :=
  match wl with
  | .NotLocked _ => reader_count = pos_reader_count
  | _ => reader_count = pos_reader_count - W32 rwmutexMaxReadersZ

def ownRWMutexInvariantDef (γ : RWMutexProtocolNames)
    (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex) : IProp GF :=
  iprop(∃ (wl : WlockState) (pos_reader_count : w32) (outstanding_reader_wait : Nat),
    "Houtstanding" ∷ ownTokAuth γ.readWaitGn outstanding_reader_wait ∗
    "Hwl" ∷ ghostVar γ.wlockGn (1 : Qp).half wl ∗
    "Hrlock_overflow" ∷ ownTokAuth γ.rlockOverflowGn (Int.toNat actualMaxReaders) ∗
    "Hrlocks" ∷ ownToks γ.rlockOverflowGn (Int.toNat (sint.Z pos_reader_count)) ∗
    "%Hpos_reader_count_pos" ∷ ⌜0 ≤ sint.Z pos_reader_count ∧
      sint.Z pos_reader_count < rwmutexMaxReadersZ⌝ ∗
    "%Hreader_count" ∷ ⌜RwReaderCountRel wl reader_count pos_reader_count⌝ ∗
    "Hreaders" ∷ rwInvReaders state reader_sem pos_reader_count ∗
    "Houts" ∷ rwInvOutstanding wl outstanding_reader_wait ∗
    "Hwr" ∷ rwInvWriter γ wl ∗
    "Hmain" ∷ rwInvMain γ writer_sem reader_sem reader_wait pos_reader_count
      outstanding_reader_wait wl state)
@[irreducible] def ownRWMutexInvariant (γ : RWMutexProtocolNames)
    (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex) : IProp GF :=
  ownRWMutexInvariantDef γ writer_sem reader_sem reader_count reader_wait state
theorem ownRWMutexInvariant_unseal :
    @ownRWMutexInvariant GF _ = @ownRWMutexInvariantDef GF _ := by
  funext; with_unfolding_all rfl

instance rwInvReaders_timeless (state : rwmutex) (rs p : w32) :
    Timeless (rwInvReaders (GF := GF) state rs p) := by
  cases state <;> simp only [rwInvReaders, named] <;> infer_instance
instance rwInvOutstanding_timeless (wl : WlockState) (o : Nat) :
    Timeless (rwInvOutstanding (GF := GF) wl o) := by
  cases wl <;> simp only [rwInvOutstanding, named] <;> infer_instance
instance rwInvWriter_timeless (γ : RWMutexProtocolNames) (wl : WlockState) :
    Timeless (rwInvWriter (GF := GF) γ wl) := by
  cases wl <;> simp only [rwInvWriter, named] <;> infer_instance
instance rwInvMain_timeless γ ws rs rw p o (wl : WlockState) (state : rwmutex) :
    Timeless (rwInvMain (GF := GF) γ ws rs rw p o wl state) := by
  cases wl <;> cases state <;> simp only [rwInvMain, named] <;> infer_instance

instance ownRWMutexInvariant_timeless γ a b c d e :
    Timeless (ownRWMutexInvariant (GF := GF) γ a b c d e) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef named; infer_instance

-- Close a goal made of (named) pure facts about the counters with `word`.
local macro "rw_pure_finish" : tactic => `(tactic| (
  (try simp only [named])
  ipureintro
  (try simp only [rwmutexMaxReadersZ, actualMaxReaders_unseal] at *)
  and_intros <;> (try subst_vars) <;> word))

-- Case on `state` and `wl` and reduce the invariant's `match`es.
-- Re-establish the invariant with the given `wl`, `pos_reader_count` and
-- `outstanding_reader_wait`.
set_option hygiene false in
local macro "rw_reestablish " wl:term:max pos:term:max o:term:max : tactic => `(tactic| (
  iexists $wl, $pos, $o
  simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel]
  iframe
  (try simp only [named])
  (try iframe Hwriter)
  rw_pure_finish))

-- (`dsimp`: the `match`es reduce definitionally, so no rewriting proofs through the
-- whole Iris context are built.)
local macro "rw_unfold_cases" : tactic => `(tactic| (
  cases ‹rwmutex› <;> cases ‹WlockState› <;>
  dsimp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
    RwReaderCountRel] at *))

theorem step_RLock_readerCount_Add (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ownToks (GF := GF) γ.rlockOverflowGn 1 ∗ ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> (if 0 ≤ sint.Z (rc + W32 1) then
       iprop(∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
         "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 1) rwt (.RLocked (n + 1)))
     else iprop("Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 1) rwt state)) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hrlock, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  icombine Hrlock Hrlocks as Hrlocks
  icombine Hrlock_overflow Hrlocks gives %Hoverflow
  rw [actualMaxReaders_unseal] at Hoverflow
  have e : Int.toNat (sint.Z (pos + W32 1)) = 1 + Int.toNat (sint.Z pos) := by
    simp only [rwmutexMaxReadersZ] at *; word
  rw [← e]
  rw_unfold_cases
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    rw [if_pos (by subst Hreader_count; simp only [rwmutexMaxReadersZ] at *; word)]
    iexists n
    isplitr
    · ipureintro; rfl
    iexists (.NotLocked r), pos + W32 1, o
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel]
    iframe
    rw_pure_finish
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReadersZ] at *; word)]
    iexists (.SignalingReaders r), pos + W32 1, o
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel]
    iframe
    rw_pure_finish
  · rename_i n
    iNamed Hreaders; iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReadersZ] at *; word)]
    iexists .WaitingForReaders, pos + W32 1, o
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel]
    iframe
    (try simp only [named])
    iframe Hwriter
    rw_pure_finish
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReadersZ] at *; word)]
    iexists .IsLocked, pos + W32 1, o
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel]
    iframe
    rw_pure_finish

theorem step_RLock_readerSem_Semacquire (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) (Hsem_acq : 0 < uint.Z rs) :
    ownRWMutexInvariant (GF := GF) γ ws rs rc rwt state ⊢
    |==> ∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws (rs - W32 1) rc rwt (.RLocked (n + 1)) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨%wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  rw_unfold_cases
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    iexists n; isplitr
    · ipureintro; rfl
    rw_reestablish (.NotLocked r) pos o
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    iexists n; isplitr
    · ipureintro; rfl
    rw_reestablish (.SignalingReaders r) pos o
  · rename_i n
    iNamed Hreaders; iNamed Hmain
    iexists n; isplitr
    · ipureintro; rfl
    rw_reestablish .WaitingForReaders pos o
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iNamed Hmain
    exfalso; obtain ⟨_, _, h⟩ := Hlocked; subst h; word

theorem step_TryRLock_readerCount_CompareAndSwap (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) (Hpos : 0 ≤ sint.Z rc) :
    ownToks (GF := GF) γ.rlockOverflowGn 1 ∗ ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 1) rwt (.RLocked (n + 1)) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hrlock, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  icombine Hrlock Hrlocks as Hrlocks
  icombine Hrlock_overflow Hrlocks gives %Hoverflow
  rw [actualMaxReaders_unseal] at Hoverflow
  have e : Int.toNat (sint.Z (pos + W32 1)) = 1 + Int.toNat (sint.Z pos) := by
    simp only [rwmutexMaxReadersZ] at *; word
  rw [← e]
  rw_unfold_cases
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    iexists n; isplitr
    · ipureintro; rfl
    rw_reestablish (.NotLocked r) (pos + W32 1) o
  all_goals first
    | (iexfalso; iexact Hmain)
    | (exfalso; subst_vars; simp only [rwmutexMaxReadersZ] at *; word)

theorem rw_neg_after_sub (pos : w32) (h : 0 ≤ sint.Z pos ∧ sint.Z pos < rwmutexMaxReadersZ) :
    sint.Z (pos - W32 rwmutexMaxReadersZ + W32 (-1)) < 0 := by
  simp only [rwmutexMaxReadersZ] at *; word

theorem step_RUnlock_readerCount_Add (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (num_readers : Nat) :
    ownRWMutexInvariant (GF := GF) γ ws rs rc rwt (.RLocked (num_readers + 1)) ⊢
    |==> ("Hrtok" ∷ ownToks γ.rlockOverflowGn 1 ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 (-1)) rwt (.RLocked num_readers) ∗
      (if sint.Z (rc + W32 (-1)) < 0 then
        iprop("Hwait_tok" ∷ ownToks γ.readWaitGn 1 ∗
          "%" ∷ ⌜sint.Z rc ≠ 0⌝ ∗ "%" ∷ ⌜sint.Z rc ≠ -rwmutexMaxReadersZ⌝)
      else iprop(True))) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨%wl, %pos, %o, Hinv⟩
  iNamed Hinv
  simp only [rwInvReaders]
  iNamed Hreaders
  have e : Int.toNat (sint.Z pos) = 1 + Int.toNat (sint.Z (pos - W32 1)) := by
    simp only [rwmutexMaxReadersZ] at *; word
  rw [e]
  icases (ownToks_add _ 1 _).1 $$ Hrlocks with ⟨Hr, Hrlocks⟩
  cases wl
  · rename_i r
    simp only [rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel] at *
    iNamed Hmain
    rw [if_neg (by subst_vars; simp only [rwmutexMaxReadersZ] at *; word)]
    imodintro
    iframe Hr
    isplitl
    · rw_reestablish (.NotLocked r) (pos - W32 1) o
    · itrivial
  · rename_i r
    simp only [rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel] at *
    iNamed Hmain
    rw [if_pos (by subst_vars; exact rw_neg_after_sub _ Hpos_reader_count_pos)]
    imod ownTokAuth_add 1 γ.readWaitGn o $$ Houtstanding with ⟨Houtstanding, Hwt⟩
    imodintro
    iframe Hr
    isplitr [Hwt]
    · rw_reestablish (.SignalingReaders r) (pos - W32 1) (o + 1)
    · iframe Hwt; rw_pure_finish
  · simp only [rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel] at *
    iNamed Hmain
    rw [if_pos (by subst_vars; exact rw_neg_after_sub _ Hpos_reader_count_pos)]
    imod ownTokAuth_add 1 γ.readWaitGn o $$ Houtstanding with ⟨Houtstanding, Hwt⟩
    imodintro
    iframe Hr
    isplitr [Hwt]
    · rw_reestablish .WaitingForReaders (pos - W32 1) (o + 1)
    · iframe Hwt; rw_pure_finish
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

theorem step_rUnlockSlow_readerWait_Add (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ownToks (GF := GF) γ.readWaitGn 1 ∗ ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ("Hprot_inv" ∷ ownRWMutexInvariant γ ws rs rc (rwt + W32 (-1)) state ∗
      (if rwt + W32 (-1) = W32 0 then
        iprop("Hwtok" ∷ ghostVar γ.writerSemTokGn (1 : Qp).half ())
      else iprop("_" ∷ True))) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwait_tok, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Houtstanding Hwait_tok gives %Hle
  rw_unfold_cases
  · iNamed Houts; exfalso; omega
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    imod ownTokAuth_delete_S γ.readWaitGn o' $$ Houtstanding Hwait_tok with Houtstanding
    rw [if_neg (by simp only [rwmutexMaxReadersZ] at *; word)]
    imodintro
    isplitl
    · rw_reestablish (.SignalingReaders r) pos o'
    · itrivial
  · rename_i n
    iNamed Hreaders; iNamed Hmain
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    imod ownTokAuth_delete_S γ.readWaitGn o' $$ Houtstanding Hwait_tok with Houtstanding
    icases Hwriter with (Hwriter | ⟨_, %Hbad⟩)
    · by_cases hz : rwt + W32 (-1) = W32 0
      · rw [if_pos hz]
        icases (ghostVar_split γ.writerSemTokGn () (1 : Qp).half (1 : Qp).half) $$ [Hwriter]
          with ⟨Hw1, Hw2⟩
        · rw [Qp.half_add_half]; iexact Hwriter
        imodintro
        ihave Hwriter : iprop(ghostVar γ.writerSemTokGn 1 () ∨
            (ghostVar γ.writerSemTokGn (1 : Qp).half () ∗
              ⌜ws = W32 0 ∧ rwt + W32 (-1) = W32 0⌝)) $$ [Hw1]
        · iright; iframe Hw1; ipureintro; simp only [rwmutexMaxReadersZ] at *; and_intros <;> word
        isplitr [Hw2]
        · rw_reestablish .WaitingForReaders pos o'
        · iframe Hw2
      · rw [if_neg hz]
        imodintro
        isplitl
        · rw_reestablish .WaitingForReaders pos o'
        · itrivial
    · exfalso; obtain ⟨_, h⟩ := Hbad; subst h; simp only [rwmutexMaxReadersZ] at *; word
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iNamed Houts; exfalso; omega

theorem step_rUnlockSlow_writerSem_Semrelease (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ghostVar (GF := GF) γ.writerSemTokGn (1 : Qp).half () ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ("Hprot_inv" ∷ ownRWMutexInvariant γ (ws + W32 1) rs rc rwt state) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwriter_tok, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  rw_unfold_cases
  all_goals first
    | (iexfalso; iexact Hmain)
    | (iNamed Hwr; icombine Hwriter_unused Hwriter_tok gives % ⟨Hbad, _⟩;
       exfalso; have : (1 : Rat) + 1 / 2 ≤ 1 := Hbad; grind)
    | skip
  rename_i n
  iNamed Hreaders; iNamed Hmain
  icases Hwriter with (Hbad | ⟨Hwriter, %Hp⟩)
  · icombine Hbad Hwriter_tok gives % ⟨Hbad, _⟩
    exfalso; have : (1 : Rat) + 1 / 2 ≤ 1 := Hbad; grind
  · icombine Hwriter Hwriter_tok as Hwriter
    obtain ⟨h1, h2⟩ := Hp
    subst h1 h2
    ihave Hwriter : iprop(ghostVar γ.writerSemTokGn 1 () ∨
        (ghostVar γ.writerSemTokGn (1 : Qp).half () ∗
          ⌜W32 0 + W32 1 = W32 0 ∧ W32 0 = W32 0⌝)) $$ [Hwriter]
    · ileft; iexact Hwriter
    rw [show (W32 0 + W32 1 : w32) = W32 1 from rfl]
    rw_reestablish .WaitingForReaders pos o

theorem step_Lock_readerCount_Add (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)) ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> (if rc = W32 0 then
      iprop("%" ∷ ⌜state = .RLocked 0⌝ ∗
        "Hwl_inv" ∷ ghostVar γ.wlockGn (1 : Qp).half WlockState.IsLocked ∗
        "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 (-rwmutexMaxReadersZ)) rwt .Locked)
    else
      iprop("Hwl" ∷ ghostVar γ.wlockGn (1 : Qp).half
          (WlockState.SignalingReaders (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)) ∗
        "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 (-rwmutexMaxReadersZ)) rwt state)) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
      RwReaderCountRel] at *
    iNamed Hreaders; iNamed Houts; iNamed Hwr; iNamed Hmain
    by_cases hz : rc = W32 0
    · rw [if_pos hz]
      imod ghostVar_update_halves WlockState.IsLocked γ.wlockGn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      have hn : n = 0 := by subst_vars; simp only [rwmutexMaxReadersZ] at *; word
      subst hn
      imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish WlockState.IsLocked pos o
    · rw [if_neg hz]
      imod ghostVar_update_halves
        (WlockState.SignalingReaders (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ))
        γ.wlockGn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      imodintro
      iframe Hwl_in
      rw_reestablish (WlockState.SignalingReaders
        (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)) pos o
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

theorem step_Lock_readerWait_Add (γ : RWMutexProtocolNames) (r ws rs rc rwt : w32)
    (state : rwmutex) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half (WlockState.SignalingReaders r) ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> (if sint.Z (rwt + r) = 0 then
      iprop("%" ∷ ⌜state = .RLocked 0⌝ ∗
        "Hwl_inv" ∷ ghostVar γ.wlockGn (1 : Qp).half WlockState.IsLocked ∗
        "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs rc (rwt + r) .Locked)
    else
      iprop("Hwl" ∷ ghostVar γ.wlockGn (1 : Qp).half WlockState.WaitingForReaders ∗
        "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs rc (rwt + r) state)) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
      RwReaderCountRel] at *
    iNamed Hreaders; iNamed Hwr; iNamed Hmain
    by_cases hz : sint.Z (rwt + r) = 0
    · rw [if_pos hz]
      imod ghostVar_update_halves WlockState.IsLocked γ.wlockGn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      have hn : n = 0 ∧ o = 0 := by simp only [rwmutexMaxReadersZ] at *; constructor <;> word
      obtain ⟨rfl, rfl⟩ := hn
      imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish WlockState.IsLocked pos 0
    · rw [if_neg hz]
      imod ghostVar_update_halves WlockState.WaitingForReaders γ.wlockGn _ _ $$ Hwl Hwl_in
        with ⟨Hwl, Hwl_in⟩
      imodintro
      iframe Hwl_in
      ihave Hwriter : iprop(ghostVar γ.writerSemTokGn 1 () ∨
          (ghostVar γ.writerSemTokGn (1 : Qp).half () ∗
            ⌜ws = W32 0 ∧ rwt + r = W32 0⌝)) $$ [Hwriter_unused]
      · ileft; iexact Hwriter_unused
      rw_reestablish .WaitingForReaders pos o
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

theorem step_Lock_writerSem_Semacquire (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) (Hsem : 0 < uint.Z ws) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half WlockState.WaitingForReaders ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ("%" ∷ ⌜state = .RLocked 0⌝ ∗
      "Hwl_inv" ∷ ghostVar γ.wlockGn (1 : Qp).half WlockState.IsLocked ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ (ws - W32 1) rs rc rwt .Locked) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
      RwReaderCountRel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghostVar_update_halves WlockState.IsLocked γ.wlockGn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    have hn : n = 0 ∧ o = 0 := by simp only [rwmutexMaxReadersZ] at *; constructor <;> word
    obtain ⟨rfl, rfl⟩ := hn
    icases Hwriter with (Hwriter_unused | ⟨_, %Hbad⟩)
    · imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish WlockState.IsLocked pos 0
    · exfalso; obtain ⟨h, _⟩ := Hbad; subst h; simp only [rwmutexMaxReadersZ] at *; word
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

theorem step_TryLock_readerCount_CompareAndSwap (γ : RWMutexProtocolNames) (ws rs rc rwt : w32)
    (state : rwmutex) (Hz : sint.Z rc = 0) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)) ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ("%" ∷ ⌜state = .RLocked 0⌝ ∗
      "Hwl_inv" ∷ ghostVar γ.wlockGn (1 : Qp).half WlockState.IsLocked ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 (-rwmutexMaxReadersZ)) rwt .Locked) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
      RwReaderCountRel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghostVar_update_halves WlockState.IsLocked γ.wlockGn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    have hn : n = 0 := by subst_vars; simp only [rwmutexMaxReadersZ] at *; word
    subst hn
    imodintro
    isplitr
    · ipureintro; rfl
    iframe Hwl_in
    rw_reestablish WlockState.IsLocked pos o
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

theorem step_Unlock_readerCount_Add (γ : RWMutexProtocolNames) (ws rs rc rwt : w32) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half WlockState.IsLocked ∗
      ownRWMutexInvariant γ ws rs rc rwt .Locked ⊢
    |==> ("Hwl" ∷ ghostVar γ.wlockGn (1 : Qp).half
        (WlockState.NotLocked (rc + W32 rwmutexMaxReadersZ)) ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws rs (rc + W32 rwmutexMaxReadersZ) rwt (.RLocked 0) ∗
      "%" ∷ ⌜0 ≤ sint.Z (rc + W32 rwmutexMaxReadersZ)⌝ ∗
      "%" ∷ ⌜sint.Z (rc + W32 rwmutexMaxReadersZ) < rwmutexMaxReadersZ⌝) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
    RwReaderCountRel] at *
  iNamed Hmain
  imod ghostVar_update_halves (WlockState.NotLocked (rc + W32 rwmutexMaxReadersZ)) γ.wlockGn _ _
    $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
  imodintro
  iframe Hwl_in
  isplitl
  · rw_reestablish (WlockState.NotLocked (rc + W32 rwmutexMaxReadersZ)) pos o
  · rw_pure_finish

theorem step_Unlock_readerSem_Semrelease (γ : RWMutexProtocolNames) (ws rs rc rwt r : w32)
    (state : rwmutex) (Hpos : 0 < sint.Z r) :
    ghostVar (GF := GF) γ.wlockGn (1 : Qp).half (WlockState.NotLocked r) ∗
      ownRWMutexInvariant γ ws rs rc rwt state ⊢
    |==> ("Hwl" ∷ ghostVar γ.wlockGn (1 : Qp).half (WlockState.NotLocked (r - W32 1)) ∗
      "Hprot_inv" ∷ ownRWMutexInvariant γ ws (rs + W32 1) rc rwt state) := by
  rw [ownRWMutexInvariant_unseal]; unfold ownRWMutexInvariantDef
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain,
      RwReaderCountRel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghostVar_update_halves (WlockState.NotLocked (r - W32 1)) γ.wlockGn _ _
      $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    imodintro
    iframe Hwl_in
    rw_reestablish (WlockState.NotLocked (r - W32 1)) pos o
  · simp only [rwInvMain]
    iexfalso; iexact Hmain

end protocol

theorem mask_inv_sema (N : Namespace) : (↑(N.@"inv") : CoPset) ⊆ ⊤ \ ↑(N.@"sema") := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, fun h => ndot_ne_disjoint N (by decide : "inv" ≠ "sema") p ⟨hp, h⟩⟩




theorem sext_32_64 (x : w32) : sint.Z (W64 (sint.Z x)) = sint.Z x := by
  simp only [W64, sint.Z, BitVec.toInt_ofInt]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  apply Int.bmod_eq_of_le <;> simp at * <;> omega

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def ownRWMutexDef (γ : RWMutexNames) (state : rwmutex) : IProp GF :=
  ghostVar γ.protGn.stateGn (1 : Qp).half state
@[irreducible] def ownRWMutex (γ : RWMutexNames) (state : rwmutex) : IProp GF :=
  ownRWMutexDef γ state
theorem ownRWMutex_unseal : ownRWMutex (GF := GF) = ownRWMutexDef (GF := GF) := by
  funext; with_unfolding_all rfl
instance ownRWMutex_timeless (γ : RWMutexNames) (state : rwmutex) :
    Timeless (ownRWMutex (GF := GF) γ state) := by
  rw [ownRWMutex_unseal]; unfold ownRWMutexDef; infer_instance

def ownRLockTokenDef (γ : RWMutexNames) : IProp GF := ownToks γ.protGn.rlockOverflowGn 1
@[irreducible] def ownRLockToken (γ : RWMutexNames) : IProp GF := ownRLockTokenDef γ
theorem ownRLockToken_unseal : ownRLockToken (GF := GF) = ownRLockTokenDef (GF := GF) := by
  funext; with_unfolding_all rfl

abbrev RWW (rw : Loc) : Loc := structFieldRef RWMutex go!"w" rw
abbrev RWReaderSem (rw : Loc) : Loc := structFieldRef RWMutex go!"readerSem" rw
abbrev RWWriterSem (rw : Loc) : Loc := structFieldRef RWMutex go!"writerSem" rw
abbrev RWReaderCount (rw : Loc) : Loc := structFieldRef RWMutex go!"readerCount" rw
abbrev RWReaderWait (rw : Loc) : Loc := structFieldRef RWMutex go!"readerWait" rw

abbrev rwLockedPart (rw : Loc) (γ : RWMutexNames) (state : rwmutex) : IProp GF :=
  match state with
  | .Locked => iprop(ownMutex (RWW (GF := GF) rw) ∗
      ghostVar γ.protGn.wlockGn (1 : Qp).half WlockState.IsLocked)
  | _ => iprop(True)

abbrev rwInv (rw : Loc) (γ : RWMutexNames) : IProp GF :=
  iprop(∃ (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex),
    "Hstate" ∷ ghostVar γ.protGn.stateGn (1 : Qp).half state ∗
    "HreaderSem" ∷ ownSema γ.readerSemGn reader_sem ∗
    "HwriterSem" ∷ ownSema γ.writerSemGn writer_sem ∗
    "HreaderCount" ∷ sync.atomic.ownInt32 (RWReaderCount (GF := GF) rw) (DFrac.own 1) reader_count ∗
    "HreaderWait" ∷ sync.atomic.ownInt32 (RWReaderWait (GF := GF) rw) (DFrac.own 1) reader_wait ∗
    "Hprot" ∷ ownRWMutexInvariant γ.protGn writer_sem reader_sem reader_count reader_wait state ∗
    "Hlocked" ∷ rwLockedPart rw γ state)

instance rwLockedPart_timeless (rw : Loc) (γ : RWMutexNames) (state : rwmutex) :
    Timeless (rwLockedPart (GF := GF) rw γ state) := by
  cases state <;> simp only [rwLockedPart] <;> infer_instance

instance rwInv_timeless (rw : Loc) (γ : RWMutexNames) : Timeless (rwInv (GF := GF) rw γ) := by
  unfold rwInv named; infer_instance

def isRWMutexDef (rw : Loc) (γ : RWMutexNames) (N : Namespace) : IProp GF :=
  iprop("#Hmu" ∷ isMutex (RWW (GF := GF) rw)
      (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0))) ∗
    "#His_readerSem" ∷ isSema (RWReaderSem (GF := GF) rw) γ.readerSemGn (N.@"sema") ∗
    "#His_writerSem" ∷ isSema (RWWriterSem (GF := GF) rw) γ.writerSemGn (N.@"sema") ∗
    "#Hinv" ∷ inv (N.@"inv") (rwInv rw γ))
@[irreducible] def isRWMutex (rw : Loc) (γ : RWMutexNames) (N : Namespace) : IProp GF :=
  isRWMutexDef rw γ N
theorem isRWMutex_unseal : @isRWMutex = @isRWMutexDef := by funext; with_unfolding_all rfl

instance isRWMutex_pers (rw : Loc) (γ : RWMutexNames) (N : Namespace) :
    Persistent (isRWMutex (GF := GF) rw γ N) := by
  rw [isRWMutex_unseal]; unfold isRWMutexDef named; infer_instance

theorem ownToks_replicate (γ : GName) (n : Nat) :
    ownToks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), ownToks γ 1 := by
  induction n with
  | zero => simp only [List.replicate]; exact BigSepL.bigSepL_nil_intro
  | succ n ih =>
    iintro H
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    icases (ownToks_add n 1 γ).1 $$ [H] with ⟨H1, H2⟩
    · rw [Nat.add_comm]; iexact H
    iframe H1
    iapply ih $$ H2

theorem init_RWMutex {E : CoPset} (N : Namespace) (rw : Loc) :
    typedPointsto (GF := GF) rw (zero_val RWMutex) (DFrac.own 1) ⊢
    |={E}=> ∃ γ : RWMutexNames, isRWMutex rw γ N ∗ ownRWMutex γ (.RLocked 0) ∗
      [∗list] _x ∈ List.replicate (Int.toNat actualMaxReaders) (), ownRLockToken γ := by
  iintro Hrw
  iStructNamed Hrw
  rw [show (zero_val RWMutex).readerSem' = W32 0 from rfl,
    show (zero_val RWMutex).writerSem' = W32 0 from rfl,
    show (zero_val RWMutex).readerCount' =
      ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) from rfl,
    show (zero_val RWMutex).readerWait' =
      ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32) from rfl]
  imod ownTokAuth_alloc (GF := GF) with ⟨%γread_wait, Hread_wait⟩
  imod ownTokAuth_alloc (GF := GF) with ⟨%γrlock, Hrlock⟩
  imod ownTokAuth_add (Int.toNat actualMaxReaders) γrlock 0 $$ Hrlock with ⟨Hrlock, Htoks⟩
  imod ghostVar_alloc (WlockState.NotLocked (W32 0)) with ⟨%γwl, Hwl⟩
  icases ghostVar_split γwl (WlockState.NotLocked (W32 0)) (1 : Qp).half (1 : Qp).half $$ [Hwl]
    with ⟨Hwl, Hwl_inv⟩
  · rw [Qp.half_add_half]; iexact Hwl
  imod ghostVar_alloc (rwmutex.RLocked 0) with ⟨%γst, Hst⟩
  icases ghostVar_split γst (rwmutex.RLocked 0) (1 : Qp).half (1 : Qp).half $$ [Hst]
    with ⟨Hst, Hst_inv⟩
  · rw [Qp.half_add_half]; iexact Hst
  imod ghostVar_alloc () with ⟨%γwt, Hwt⟩
  imod init_sema (E := E) (N.@"sema") (RWReaderSem rw) (W32 0) $$ readerSem with ⟨%γrs, #Hrs, Hrs_own⟩
  imod init_sema (E := E) (N.@"sema") (RWWriterSem rw) (W32 0) $$ writerSem with ⟨%γws, #Hws, Hws_own⟩
  let γ : RWMutexNames := ⟨⟨γread_wait, γrlock, γwl, γwt, γst⟩, γrs, γws⟩
  imod init_Mutex (ghostVar γwl (1 : Qp).half (WlockState.NotLocked (W32 0))) E (RWW rw)
    $$ w [Hwl] with #Hmu
  · inext; iexact Hwl
  imod ownToks_0 (GF := GF) γrlock with H0
  ihave Hprot : ownRWMutexInvariant (GF := GF) γ.protGn (W32 0) (W32 0) (W32 0) (W32 0)
      (rwmutex.RLocked 0) $$ [Hread_wait Hwl_inv Hrlock H0 Hwt]
  · simp only [ownRWMutexInvariant_unseal, ownRWMutexInvariantDef]
    iexists (WlockState.NotLocked (W32 0)), (W32 0), 0
    simp only [rwInvReaders, rwInvOutstanding, rwInvWriter, rwInvMain, RwReaderCountRel,
      Nat.zero_add, show (sint.Z (W32 0)).toNat = 0 from rfl]
    iframe
    simp only [named]
    ipureintro
    simp only [rwmutexMaxReadersZ]
    and_intros <;> word
  imod inv_alloc (N.@"inv") E (rwInv rw γ) $$ [Hst_inv Hrs_own Hws_own readerCount readerWait
      Hprot] with #Hinv
  · inext
    iexists (W32 0), (W32 0), (W32 0), (W32 0), (rwmutex.RLocked 0)
    simp only [rwLockedPart, sync.atomic.ownInt32_unseal, sync.atomic.ownInt32Def]
    iframe
  imodintro
  iexists γ
  simp only [isRWMutex_unseal, isRWMutexDef, ownRWMutex_unseal, ownRWMutexDef,
    ownRLockToken_unseal, ownRLockTokenDef]
  iframe Hst
  iframe #
  iapply ownToks_replicate $$ Htoks

end wps

end rwmutex

end sync

end Perennial
end