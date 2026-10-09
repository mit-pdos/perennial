/-
`sync.RWMutex`, with a logically
atomic specification over an abstract `rwmutex` state.
-/
module

public import Perennial.Proof.sync_proof.base
public import Perennial.Proof.sync_proof.mutex
public import Perennial.Proof.sync_proof.sema
public import Perennial.Proof.sync.atomic

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def ownRWMutexDef (γ : RWMutexNames) (state : rwmutex) : IProp GF :=
  ghostVar γ.protGn.stateGn (1 : Qp).half state
@[irreducible] def ownRWMutex (γ : RWMutexNames) (state : rwmutex) : IProp GF :=
  ownRWMutexDef γ state
theorem ownRWMutex_unseal : @ownRWMutex GF _ = @ownRWMutexDef GF _ := by
  funext; with_unfolding_all rfl
instance ownRWMutex_timeless (γ : RWMutexNames) (state : rwmutex) :
    Timeless (ownRWMutex (GF := GF) γ state) := by
  rw [ownRWMutex_unseal]; unfold ownRWMutexDef; infer_instance

def ownRLockTokenDef (γ : RWMutexNames) : IProp GF := ownToks γ.protGn.rlockOverflowGn 1
@[irreducible] def ownRLockToken (γ : RWMutexNames) : IProp GF := ownRLockTokenDef γ
theorem ownRLockToken_unseal : @ownRLockToken GF _ = @ownRLockTokenDef GF _ := by
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

theorem RWMutex.wp_RLock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N ∗ ownRLockToken γ) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ state, ownRWMutex γ state ∗
          (∀ num_readers, ⌜state = .RLocked num_readers⌝ →
            ownRWMutex γ (.RLocked (num_readers + 1)) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RLock")) (Val #())) {{ Φ }} := by
  wp_start as ⟨#His, Htok⟩
  simp only [isRWMutex_unseal, isRWMutexDef, ownRLockToken_unseal, ownRLockTokenDef]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with _
  imod step_RLock_readerCount_Add γ.protGn ws rs rc rwt state $$ [Htok Hprot] with Hprot_inv
  · iframe
  by_cases h : 0 ≤ sint.Z (rc + W32 1)
  · -- fast path
    simp only [h, ↓reduceIte]
    icases Hprot_inv with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 1), rwt, (rwmutex.RLocked (n + 1))
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : ¬ (sint.Z (rc + W32 1) < sint.Z (W32 0)) := by word
    simp only [h', decide_false]
    wp_auto
    iexact HΦ
  · -- slow path
    simp only [h, ↓reduceIte]
    iNamed Hprot_inv
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot_inv Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 1), rwt, state
      iframe
    imodintro
    wp_auto
    have h' : sint.Z (rc + W32 1) < sint.Z (W32 0) := by word
    simp only [h', decide_true]
    wp_auto
    wp_apply_core wp_runtime_SemacquireRWMutexR (RWReaderSem rw) γ.readerSemGn (N.@"sema")
      false (W64 0) $$ [] [-]
    · iframe #
    iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
    icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists rs
    iframe HreaderSem
    iintro %Hpos HreaderSem
    imod Hmask with _
    imod step_RLock_readerSem_Semacquire γ.protGn ws rs rc rwt state
      (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ Hprot with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, (rs - W32 1), rc, rwt, (rwmutex.RLocked (n + 1))
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    iexact HΦ

theorem RWMutex.wp_TryRLock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N ∗ ownRLockToken γ) -∗
      ▷ ((|={⊤ \ ↑N,∅}=> ∃ state, ownRWMutex γ state ∗
          (∀ num_readers, ⌜state = .RLocked num_readers⌝ →
            ownRWMutex γ (.RLocked (num_readers + 1)) ={∅,⊤ \ ↑N}=∗ Φ #true)) ∧
         Φ #false) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"TryRLock")) (Val #())) {{ Φ }} := by
  wp_start as ⟨#His, Htok⟩
  simp only [isRWMutex_unseal, isRWMutexDef, ownRLockToken_unseal, ownRLockTokenDef]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_for
  wp_apply_core sync.atomic.Int32.wp_Load $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with _
  imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
  · inext
    iexists ws, rs, rc, rwt, state
    iframe
  imodintro
  wp_auto
  wp_if_destruct
  · wp_for_post
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  · wp_apply_core sync.atomic.Int32.wp_CompareAndSwap $$ [] [-]
    · iPkgInit
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc', %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rc', (DFrac.own 1)
    iframe HreaderCount
    isplitr
    · ipureintro; split <;> rfl
    iintro HreaderCount
    by_cases hc : rc' = rc
    · subst hc
      simp only [↓reduceIte, decide_true]
      imod step_TryRLock_readerCount_CompareAndSwap γ.protGn ws rs rc' rwt state
        (by word) $$ [Htok Hprot] with ⟨%n, %Hst, Hprot⟩
      · iframe
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [ownRWMutex_unseal, ownRWMutexDef]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghostVar_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ %n [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, (rc' + W32 1), rwt, (rwmutex.RLocked (n + 1))
        simp only [rwLockedPart]
        iframe
      imodintro
      wp_auto
      wp_for_post
      iexact HΦ
    · simp only [hc, ↓reduceIte, decide_false]
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc', rwt, state
        iframe
      imodintro
      wp_auto
      wp_for_post
      iframe

set_option maxRecDepth 200000 in
theorem RWMutex.wp_RUnlock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ num_readers, ownRWMutex γ (.RLocked (num_readers + 1)) ∗
          (ownRWMutex γ (.RLocked num_readers) ∗ ownRLockToken γ ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"RUnlock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef, ownRLockToken_unseal, ownRLockTokenDef]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with _
  imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
  imod HΦ with ⟨%n, Hst, HΦ⟩
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (rwmutex.RLocked n) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  ihave X := step_RUnlock_readerCount_Add γ.protGn ws rs rc rwt n $$ Hprot
  imod X with X
  by_cases hneg : sint.Z (rc + W32 (-1)) < 0
  · simp only [hneg, ↓reduceIte]
    icases X with ⟨Hrtok, Hprot, Hwait_tok, %H1, %H2⟩
    imod HΦ $$ [Hst Hrtok] with HΦ
    · iframe
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-1)), rwt, (rwmutex.RLocked n)
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : sint.Z (rc + W32 (-1)) < sint.Z (W32 0) := by word
    simp only [h', decide_true]
    wp_auto
    wp_method_call
    wp_auto
    have hA : ¬ (rc + W32 (-1) + W32 1 = W32 0) := by
      intro h; apply H1; simp only [rwmutexMaxReadersZ] at *; word
    simp only [hA, decide_false, sync.rwmutexMaxReaders]
    wp_auto
    have hB : ¬ (rc + W32 (-1) + W32 1 = W32 (-1073741824)) := by
      intro h; apply H2; simp only [rwmutexMaxReadersZ] at *; word
    simp only [hB, decide_false]
    wp_auto
    wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
    · iPkgInit
    clear hA hB h' hneg H1 H2
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc2, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rwt
    iframe HreaderWait
    iintro HreaderWait
    imod Hmask with _
    ihave X := step_rUnlockSlow_readerWait_Add γ.protGn ws rs rc2 rwt state $$ [Hwait_tok Hprot]
    · iframe
    imod X with X
    by_cases hz : rwt + W32 (-1) = W32 0
    · simp only [hz, ↓reduceIte]
      icases X with ⟨Hprot, Hwtok⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc2, (W32 0), state
        iframe
      imodintro
      wp_auto
      wp_apply_core wp_runtime_Semrelease (RWWriterSem rw) γ.writerSemGn (N.@"sema")
        false (W64 1) $$ [] [-]
      · iframe #
      iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
      icases Hi with ⟨%ws2, %rs2, %rc3, %rwt2, %state2, Hi⟩
      iNamed Hi
      ihave Y := step_rUnlockSlow_writerSem_Semrelease γ.protGn ws2 rs2 rc3 rwt2 state2
        $$ [Hwtok Hprot]
      · iframe
      imod Y with Hprot
      iapply fupd_mask_intro Std.LawfulSet.empty_subset
      iintro Hmask
      iexists ws2
      iframe HwriterSem
      iintro HwriterSem
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists (ws2 + W32 1), rs2, rc3, rwt2, state2
        iframe
      imodintro
      wp_auto
      iexact HΦ
    · simp only [hz, ↓reduceIte]
      icases X with ⟨Hprot, -⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc2, (rwt + W32 (-1)), state
        iframe
      imodintro
      wp_auto
      simp only [hz, decide_false]
      wp_auto
      iexact HΦ
  · simp only [hneg, ↓reduceIte]
    icases X with ⟨Hrtok, Hprot, -⟩
    imod HΦ $$ [Hst Hrtok] with HΦ
    · iframe
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-1)), rwt, (rwmutex.RLocked n)
      simp only [rwLockedPart]
      iframe
    imodintro
    wp_auto
    have h' : ¬ (sint.Z (rc + W32 (-1)) < sint.Z (W32 0)) := by word
    simp only [h', decide_false]
    wp_auto
    iexact HΦ

theorem RWMutex.wp_Lock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ state, ownRWMutex γ state ∗
          (⌜state = .RLocked 0⌝ → ownRWMutex γ .Locked ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Lock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply Mutex.wp_Lock (RWW rw)
    (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0))) $$ [$Hmu]
    with ⟨Hmtx, Hwl⟩
  wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with _
  ihave X := step_Lock_readerCount_Add γ.protGn ws rs rc rwt state $$ [Hwl Hprot]
  · iframe
  imod X with X
  by_cases hz : rc = W32 0
  · -- fast path
    simp only [hz, ↓reduceIte]
    icases X with ⟨%Hst, Hwl_inv, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [ownRWMutex_unseal, ownRWMutexDef]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
    · inext
      iexists ws, rs, (W32 0 + W32 (-rwmutexMaxReadersZ)), rwt, rwmutex.Locked
      simp only [rwLockedPart, named]
      iframe
    imodintro
    clear hz
    wp_auto
    iexact HΦ
  · -- slow path
    simp only [hz, ↓reduceIte]
    icases X with ⟨Hwl, Hprot⟩
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 (-rwmutexMaxReadersZ)), rwt, state
      iframe
    imodintro
    have hz' : ¬ (rc + W32 (-1073741824) + W32 1073741824 = W32 0) := by
      intro h; apply hz; word
    wp_auto
    wp_if_destruct
    · exfalso; apply hz; word
    wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
    · iPkgInit
    clear hz hz' Hif
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc', %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rwt
    iframe HreaderWait
    iintro HreaderWait
    imod Hmask with _
    ihave X := step_Lock_readerWait_Add γ.protGn (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)
      ws rs rc' rwt state $$ [Hwl Hprot]
    · iframe
    by_cases hz2 : sint.Z (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)) = 0
    · -- got the lock
      simp only [hz2, ↓reduceIte]
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [ownRWMutex_unseal, ownRWMutexDef]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)),
          rwmutex.Locked
        simp only [rwLockedPart, named]
        iframe
      imodintro
      have hz2' : rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ) = W32 0 := by
        word
      clear hz2
      wp_auto
      wp_if_destruct
      · iexact HΦ
      · exfalso; exact Hif hz2'
    · -- wait for the remaining readers
      simp only [hz2, ↓reduceIte]
      imod X with ⟨Hwl, Hprot⟩
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReadersZ) + W32 rwmutexMaxReadersZ)), state
        iframe
      imodintro
      wp_auto
      wp_if_destruct
      · exfalso; apply hz2; rw [Hif]; rfl
      · wp_apply_core wp_runtime_SemacquireRWMutex (RWWriterSem rw) γ.writerSemGn (N.@"sema")
          false (W64 0) $$ [] [-]
        · iframe #
        clear hz2 Hif
        iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
        icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
        iNamed Hi
        iapply fupd_mask_intro Std.LawfulSet.empty_subset
        iintro Hmask
        iexists ws
        iframe HwriterSem
        iintro %Hpos HwriterSem
        imod Hmask with _
        ihave Y := step_Lock_writerSem_Semacquire γ.protGn ws rs rc rwt state
          (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ [Hwl Hprot]
        · iframe
        imod Y with ⟨%Hst, Hwl_inv, Hprot⟩
        subst Hst
        imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
        imod HΦ with ⟨%st, Hst, HΦ⟩
        simp only [ownRWMutex_unseal, ownRWMutexDef]
        icombine Hst Hstate gives % ⟨_, heq⟩
        subst heq
        imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
        imod HΦ $$ [] Hst with HΦ
        · ipureintro; rfl
        imod Hmask with _
        imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
        · inext
          iexists (ws - W32 1), rs, rc, rwt, rwmutex.Locked
          simp only [rwLockedPart, named]
          iframe
        imodintro
        wp_auto
        iexact HΦ

theorem RWMutex.wp_TryLock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ ((|={⊤ \ ↑N,∅}=> ∃ state, ownRWMutex γ state ∗
          (⌜state = .RLocked 0⌝ → ownRWMutex γ .Locked ={∅,⊤ \ ↑N}=∗ Φ #true)) ∧
         Φ #false) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"TryLock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply Mutex.wp_TryLock (RWW rw)
    (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0))) $$ [$Hmu]
    with %locked Hl
  cases locked
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  · simp only [↓reduceIte]
    icases Hl with ⟨Hmtx, Hwl⟩
    wp_auto
    wp_apply_core sync.atomic.Int32.wp_CompareAndSwap $$ [] [-]
    · iPkgInit
    iinv Hinv with >Hi Hclose
    icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
    iNamed Hi
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    inext
    iexists rc, (DFrac.own 1)
    iframe HreaderCount
    isplitr
    · ipureintro; split <;> rfl
    iintro HreaderCount
    by_cases hc : rc = W32 0
    · subst hc
      simp only [↓reduceIte, decide_true]
      ihave X := step_TryLock_readerCount_CompareAndSwap γ.protGn ws rs (W32 0) rwt state rfl
        $$ [Hwl Hprot]
      · iframe
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [ownRWMutex_unseal, ownRWMutexDef]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghostVar_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      have e : W32 0 + W32 (-rwmutexMaxReadersZ) = (W32 (-1073741824) : w32) := by
        simp only [rwmutexMaxReadersZ]; word
      rw [e]
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, (W32 (-1073741824)), rwt, rwmutex.Locked
        simp only [rwLockedPart, named]
        iframe
      imodintro
      wp_auto
      iexact HΦ
    · simp only [hc, ↓reduceIte, decide_false]
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, rc, rwt, state
        iframe
      imodintro
      clear hc
      wp_auto
      wp_apply Mutex.wp_Unlock (RWW rw)
        (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)))
        $$ [$Hmu $Hmtx $Hwl]
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ

theorem RWMutex.wp_Unlock (γ : RWMutexNames) (rw : Loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ isRWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ownRWMutex γ .Locked ∗
          (ownRWMutex γ (.RLocked 0) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.GoType.PointerType RWMutex.ty @!! go!"Unlock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [isRWMutex_unseal, isRWMutexDef]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply_core sync.atomic.Int32.wp_Add $$ [] [-]
  · iPkgInit
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%ws, %rs, %rc, %rwt, %state, Hi⟩
  iNamed Hi
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists rc
  iframe HreaderCount
  iintro HreaderCount
  imod Hmask with -
  imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
  imod HΦ with ⟨Hst, HΦ⟩
  simp only [ownRWMutex_unseal, ownRWMutexDef]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghostVar_update_halves (rwmutex.RLocked 0) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  imod HΦ $$ Hst with HΦ
  imod Hmask with -
  simp only [rwLockedPart]
  icases Hlocked with ⟨Hmtx, Hwl_in⟩
  ihave X := step_Unlock_readerCount_Add γ.protGn ws rs rc rwt $$ [Hwl_in Hprot]
  · iframe
  imod X with ⟨Hwl, Hprot, %Hr1, %Hr2⟩
  imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot] with -
  · inext
    iexists ws, rs, (rc + W32 rwmutexMaxReadersZ), rwt, (rwmutex.RLocked 0)
    simp only [rwLockedPart]
    iframe
  imodintro
  wp_auto
  wp_if_destruct
  · exfalso; simp only [rwmutexMaxReadersZ] at *; word
  ihave HI : iprop(∃ (i : w64) (r2 : w32), "i" ∷ i_ptr ↦ i ∗
      "Hwl" ∷ ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked r2) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (rc + W32 rwmutexMaxReadersZ)⌝ ∗
      "%Hrr" ∷ ⌜sint.Z r2 = sint.Z (rc + W32 rwmutexMaxReadersZ) - sint.Z i⌝) $$ [i Hwl]
  · iexists (W64 0), (rc + W32 rwmutexMaxReadersZ)
    iframe
    ipureintro; simp only [rwmutexMaxReadersZ] at *; and_intros <;> word
  wp_for HI
  split
  · rename_i hlt
    simp only [decide_eq_true_eq, sext_32_64] at hlt
    wp_auto
    wp_apply_core wp_runtime_Semrelease (RWReaderSem rw) γ.readerSemGn (N.@"sema")
      false (W64 0) $$ [] [-]
    · iframe #
    have hpos : 0 < sint.Z r2 := by simp only [rwmutexMaxReadersZ] at *; word
    have hfin : (0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z (rc + W32 rwmutexMaxReadersZ)) ∧
        sint.Z (r2 - W32 1) = sint.Z (rc + W32 rwmutexMaxReadersZ) - sint.Z (i + W64 1) := by
      simp only [rwmutexMaxReadersZ] at *; and_intros <;> word
    clear Hif hlt Hr1 Hr2 Hi Hrr
    iinv Hinv with >Hi2 Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
    icases Hi2 with ⟨%ws, %rs, %rc', %rwt, %state, Hi2⟩
    iNamed Hi2
    ihave X := step_Unlock_readerSem_Semrelease γ.protGn ws rs rc' rwt r2 state hpos $$ [Hwl Hprot]
    · iframe
    imod X with ⟨Hwl, Hprot⟩
    iapply fupd_mask_intro Std.LawfulSet.empty_subset
    iintro Hmask
    iexists rs
    iframe HreaderSem
    iintro HreaderSem
    imod Hmask with -
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with -
    · inext
      iexists ws, (rs + W32 1), rc', rwt, state
      iframe
    imodintro
    wp_auto
    wp_for_post
    iframe
    iexists (i + W64 1), (r2 - W32 1)
    iframe
    ipureintro; exact hfin
  · rename_i hlt
    simp only [decide_eq_true_eq, sext_32_64] at hlt
    have hr0 : r2 = W32 0 := by simp only [rwmutexMaxReadersZ] at *; word
    subst hr0
    wp_auto
    wp_apply Mutex.wp_Unlock (RWW rw)
      (ghostVar γ.protGn.wlockGn (1 : Qp).half (WlockState.NotLocked (W32 0)))
      $$ [$Hmu $Hmtx $Hwl]
    iexact HΦ

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
