/-
Port of `new/proof/sync_proof/rwmutex.v`: `sync.RWMutex`, with a logically
atomic specification over an abstract `rwmutex` state.
-/
import Perennial.Proof.sync_proof.base
import Perennial.Proof.sync_proof.mutex
import Perennial.Proof.sync_proof.sema
import Perennial.Proof.sync.atomic

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

instance countable_wlock_state : Pos.Countable wlock_state :=
  .ofInjective (fun
      | .NotLocked r => Pos.Countable.encode ((0 : Nat), r)
      | .SignalingReaders r => Pos.Countable.encode ((1 : Nat), r)
      | .WaitingForReaders => Pos.Countable.encode ((2 : Nat), W32 0)
      | .IsLocked => Pos.Countable.encode ((3 : Nat), W32 0))
    (by rintro (a|a|_|_) (b|b|_|_) h <;> have h := Pos.encode_inj h <;> simp_all)


namespace sync

/- Rocq's `rwmutex.v` is used qualified (`rwmutex.own_RWMutex`), since
`rwmutex_guard.v` reuses the names for its fractional-resource interface. -/
namespace rwmutex

/-- Rocq `rwmutexMaxReaders` (renamed: `sync.rwmutexMaxReaders` is the Go constant). -/
abbrev rwmutexMaxReaders_Z : Int := 1073741824

/-- Rocq `actualMaxReaders` (sealed). -/
@[irreducible] def actualMaxReaders : Int := 1073741824 - 1
theorem actualMaxReaders_unseal : actualMaxReaders = 1073741824 - 1 := by
  with_unfolding_all rfl

structure RWMutex_protocol_names where
  read_wait_gn : GName
  rlock_overflow_gn : GName
  wlock_gn : GName
  writer_sem_tok_gn : GName
  state_gn : GName

section protocol
variable {GF : BundledGFunctors} [allG GF]

abbrev rw_inv_readers (state : rwmutex) (reader_sem pos_reader_count : w32) : IProp GF :=
  match state with
  | .RLocked num_readers =>
    iprop("%Hnum_readers_le" ∷ ⌜(num_readers : Int) + uint.Z reader_sem ≤ sint.Z pos_reader_count⌝)
  | _ => iprop("_" ∷ emp)

abbrev rw_inv_outstanding (wl : wlock_state) (outstanding_reader_wait : Nat) : IProp GF :=
  match wl with
  | .SignalingReaders _ | .WaitingForReaders => iprop("_" ∷ True)
  | _ => iprop("%Houtstanding_zero" ∷ ⌜outstanding_reader_wait = 0⌝)

abbrev rw_inv_writer (γ : RWMutex_protocol_names) (wl : wlock_state) : IProp GF :=
  match wl with
  | .WaitingForReaders => iprop("_" ∷ True)
  | _ => iprop("Hwriter_unused" ∷ ghost_var γ.writer_sem_tok_gn 1 ())

abbrev rw_inv_main (γ : RWMutex_protocol_names) (writer_sem reader_sem reader_wait : w32)
    (pos_reader_count : w32) (outstanding_reader_wait : Nat) (wl : wlock_state)
    (state : rwmutex) : IProp GF :=
  match wl, state with
  | .NotLocked unnotified_readers, .RLocked num_readers =>
    iprop("%Hfast" ∷ ⌜reader_wait = W32 0 ∧ writer_sem = W32 0 ∧
      sint.Z pos_reader_count = (num_readers : Int) + sint.Z unnotified_readers + uint.Z reader_sem⌝)
  | .SignalingReaders remaining_readers, .RLocked num_readers =>
    iprop("%Hblocked_unsignaled" ∷ ⌜0 ≤ sint.Z remaining_readers ∧
      sint.Z remaining_readers < rwmutexMaxReaders_Z ∧
      sint.Z reader_wait ≤ 0 ∧
      (outstanding_reader_wait : Int) + (num_readers : Int) + uint.Z reader_sem =
        sint.Z remaining_readers + sint.Z reader_wait ∧
      writer_sem = W32 0⌝)
  | .WaitingForReaders, .RLocked num_readers =>
    iprop("Hwriter" ∷ (ghost_var γ.writer_sem_tok_gn 1 () ∨
        (ghost_var γ.writer_sem_tok_gn (1 : Qp).half () ∗ ⌜writer_sem = W32 0 ∧ reader_wait = W32 0⌝)) ∗
      "%Hblocked" ∷ ⌜(outstanding_reader_wait : Int) + (num_readers : Int) + uint.Z reader_sem ≤
          sint.Z reader_wait ∧
        (writer_sem = W32 0 ∨ (writer_sem = W32 1 ∧ reader_wait = W32 0))⌝)
  | .IsLocked, .Locked =>
    iprop("%Hlocked" ∷ ⌜writer_sem = W32 0 ∧ reader_wait = W32 0 ∧ reader_sem = W32 0⌝)
  | _, _ => iprop(False)

abbrev rw_reader_count_rel (wl : wlock_state) (reader_count pos_reader_count : w32) : Prop :=
  match wl with
  | .NotLocked _ => reader_count = pos_reader_count
  | _ => reader_count = pos_reader_count - W32 rwmutexMaxReaders_Z

def own_RWMutex_invariant_def (γ : RWMutex_protocol_names)
    (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex) : IProp GF :=
  iprop(∃ (wl : wlock_state) (pos_reader_count : w32) (outstanding_reader_wait : Nat),
    "Houtstanding" ∷ own_tok_auth γ.read_wait_gn outstanding_reader_wait ∗
    "Hwl" ∷ ghost_var γ.wlock_gn (1 : Qp).half wl ∗
    "Hrlock_overflow" ∷ own_tok_auth γ.rlock_overflow_gn (Int.toNat actualMaxReaders) ∗
    "Hrlocks" ∷ own_toks γ.rlock_overflow_gn (Int.toNat (sint.Z pos_reader_count)) ∗
    "%Hpos_reader_count_pos" ∷ ⌜0 ≤ sint.Z pos_reader_count ∧
      sint.Z pos_reader_count < rwmutexMaxReaders_Z⌝ ∗
    "%Hreader_count" ∷ ⌜rw_reader_count_rel wl reader_count pos_reader_count⌝ ∗
    "Hreaders" ∷ rw_inv_readers state reader_sem pos_reader_count ∗
    "Houts" ∷ rw_inv_outstanding wl outstanding_reader_wait ∗
    "Hwr" ∷ rw_inv_writer γ wl ∗
    "Hmain" ∷ rw_inv_main γ writer_sem reader_sem reader_wait pos_reader_count
      outstanding_reader_wait wl state)
@[irreducible] def own_RWMutex_invariant (γ : RWMutex_protocol_names)
    (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex) : IProp GF :=
  own_RWMutex_invariant_def γ writer_sem reader_sem reader_count reader_wait state
theorem own_RWMutex_invariant_unseal :
    @own_RWMutex_invariant GF _ = @own_RWMutex_invariant_def GF _ := by
  funext; with_unfolding_all rfl

instance rw_inv_readers_timeless (state : rwmutex) (rs p : w32) :
    Timeless (rw_inv_readers (GF := GF) state rs p) := by
  cases state <;> simp only [rw_inv_readers, named] <;> infer_instance
instance rw_inv_outstanding_timeless (wl : wlock_state) (o : Nat) :
    Timeless (rw_inv_outstanding (GF := GF) wl o) := by
  cases wl <;> simp only [rw_inv_outstanding, named] <;> infer_instance
instance rw_inv_writer_timeless (γ : RWMutex_protocol_names) (wl : wlock_state) :
    Timeless (rw_inv_writer (GF := GF) γ wl) := by
  cases wl <;> simp only [rw_inv_writer, named] <;> infer_instance
instance rw_inv_main_timeless γ ws rs rw p o (wl : wlock_state) (state : rwmutex) :
    Timeless (rw_inv_main (GF := GF) γ ws rs rw p o wl state) := by
  cases wl <;> cases state <;> simp only [rw_inv_main, named] <;> infer_instance

instance own_RWMutex_invariant_timeless γ a b c d e :
    Timeless (own_RWMutex_invariant (GF := GF) γ a b c d e) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def named; infer_instance

-- Close a goal made of (named) pure facts about the counters with `word`.
local macro "rw_pure_finish" : tactic => `(tactic| (
  (try simp only [named])
  ipureintro
  (try simp only [rwmutexMaxReaders_Z, actualMaxReaders_unseal] at *)
  and_intros <;> (try subst_vars) <;> word))

-- Case on `state` and `wl` and reduce the invariant's `match`es
-- (Rocq: `destruct state, wl; iNamed "Hinv"`).
-- Re-establish the invariant with the given `wl`, `pos_reader_count` and
-- `outstanding_reader_wait`.
set_option hygiene false in
local macro "rw_reestablish " wl:term:max pos:term:max o:term:max : tactic => `(tactic| (
  iexists $wl, $pos, $o
  simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel]
  iframe
  (try simp only [named])
  (try iframe Hwriter)
  rw_pure_finish))

local macro "rw_unfold_cases" : tactic => `(tactic| (
  cases ‹rwmutex› <;> cases ‹wlock_state› <;>
  simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
    rw_reader_count_rel] at *))

theorem step_RLock_readerCount_Add (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) :
    own_toks (GF := GF) γ.rlock_overflow_gn 1 ∗ own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> (if 0 ≤ sint.Z (rc + W32 1) then
       iprop(∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
         "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 1) rwt (.RLocked (n + 1)))
     else iprop("Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 1) rwt state)) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hrlock, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  icombine Hrlock Hrlocks as Hrlocks
  icombine Hrlock_overflow Hrlocks gives %Hoverflow
  rw [actualMaxReaders_unseal] at Hoverflow
  have e : Int.toNat (sint.Z (pos + W32 1)) = 1 + Int.toNat (sint.Z pos) := by
    simp only [rwmutexMaxReaders_Z] at *; word
  rw [← e]
  rw_unfold_cases
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    rw [if_pos (by subst Hreader_count; simp only [rwmutexMaxReaders_Z] at *; word)]
    iexists n
    isplitr
    · ipureintro; rfl
    iexists (.NotLocked r), pos + W32 1, o
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel]
    iframe
    rw_pure_finish
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReaders_Z] at *; word)]
    iexists (.SignalingReaders r), pos + W32 1, o
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel]
    iframe
    rw_pure_finish
  · rename_i n
    iNamed Hreaders; iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReaders_Z] at *; word)]
    iexists .WaitingForReaders, pos + W32 1, o
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel]
    iframe
    (try simp only [named])
    iframe Hwriter
    rw_pure_finish
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iNamed Hmain
    rw [if_neg (by subst Hreader_count; simp only [rwmutexMaxReaders_Z] at *; word)]
    iexists .IsLocked, pos + W32 1, o
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel]
    iframe
    rw_pure_finish

theorem step_RLock_readerSem_Semacquire (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) (Hsem_acq : 0 < uint.Z rs) :
    own_RWMutex_invariant (GF := GF) γ ws rs rc rwt state ⊢
    |==> ∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws (rs - W32 1) rc rwt (.RLocked (n + 1)) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
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

theorem step_TryRLock_readerCount_CompareAndSwap (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) (Hpos : 0 ≤ sint.Z rc) :
    own_toks (GF := GF) γ.rlock_overflow_gn 1 ∗ own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ∃ n : Nat, "%" ∷ ⌜state = .RLocked n⌝ ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 1) rwt (.RLocked (n + 1)) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hrlock, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  imodintro
  icombine Hrlock Hrlocks as Hrlocks
  icombine Hrlock_overflow Hrlocks gives %Hoverflow
  rw [actualMaxReaders_unseal] at Hoverflow
  have e : Int.toNat (sint.Z (pos + W32 1)) = 1 + Int.toNat (sint.Z pos) := by
    simp only [rwmutexMaxReaders_Z] at *; word
  rw [← e]
  rw_unfold_cases
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    iexists n; isplitr
    · ipureintro; rfl
    rw_reestablish (.NotLocked r) (pos + W32 1) o
  all_goals first
    | (iexfalso; iexact Hmain)
    | (exfalso; subst_vars; simp only [rwmutexMaxReaders_Z] at *; word)

theorem rw_neg_after_sub (pos : w32) (h : 0 ≤ sint.Z pos ∧ sint.Z pos < rwmutexMaxReaders_Z) :
    sint.Z (pos - W32 rwmutexMaxReaders_Z + W32 (-1)) < 0 := by
  simp only [rwmutexMaxReaders_Z] at *; word

theorem step_RUnlock_readerCount_Add (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (num_readers : Nat) :
    own_RWMutex_invariant (GF := GF) γ ws rs rc rwt (.RLocked (num_readers + 1)) ⊢
    |==> ("Hrtok" ∷ own_toks γ.rlock_overflow_gn 1 ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 (-1)) rwt (.RLocked num_readers) ∗
      (if sint.Z (rc + W32 (-1)) < 0 then
        iprop("Hwait_tok" ∷ own_toks γ.read_wait_gn 1 ∗
          "%" ∷ ⌜sint.Z rc ≠ 0⌝ ∗ "%" ∷ ⌜sint.Z rc ≠ -rwmutexMaxReaders_Z⌝)
      else iprop(True))) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨%wl, %pos, %o, Hinv⟩
  iNamed Hinv
  simp only [rw_inv_readers]
  iNamed Hreaders
  have e : Int.toNat (sint.Z pos) = 1 + Int.toNat (sint.Z (pos - W32 1)) := by
    simp only [rwmutexMaxReaders_Z] at *; word
  rw [e]
  icases (own_toks_add _ 1 _).1 $$ Hrlocks with ⟨Hr, Hrlocks⟩
  cases wl
  · rename_i r
    simp only [rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel] at *
    iNamed Hmain
    rw [if_neg (by subst_vars; simp only [rwmutexMaxReaders_Z] at *; word)]
    imodintro
    iframe Hr
    isplitl
    · rw_reestablish (.NotLocked r) (pos - W32 1) o
    · itrivial
  · rename_i r
    simp only [rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel] at *
    iNamed Hmain
    rw [if_pos (by subst_vars; exact rw_neg_after_sub _ Hpos_reader_count_pos)]
    imod own_tok_auth_add 1 γ.read_wait_gn o $$ Houtstanding with ⟨Houtstanding, Hwt⟩
    imodintro
    iframe Hr
    isplitr [Hwt]
    · rw_reestablish (.SignalingReaders r) (pos - W32 1) (o + 1)
    · iframe Hwt; rw_pure_finish
  · simp only [rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel] at *
    iNamed Hmain
    rw [if_pos (by subst_vars; exact rw_neg_after_sub _ Hpos_reader_count_pos)]
    imod own_tok_auth_add 1 γ.read_wait_gn o $$ Houtstanding with ⟨Houtstanding, Hwt⟩
    imodintro
    iframe Hr
    isplitr [Hwt]
    · rw_reestablish .WaitingForReaders (pos - W32 1) (o + 1)
    · iframe Hwt; rw_pure_finish
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

theorem step_rUnlockSlow_readerWait_Add (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) :
    own_toks (GF := GF) γ.read_wait_gn 1 ∗ own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ("Hprot_inv" ∷ own_RWMutex_invariant γ ws rs rc (rwt + W32 (-1)) state ∗
      (if rwt + W32 (-1) = W32 0 then
        iprop("Hwtok" ∷ ghost_var γ.writer_sem_tok_gn (1 : Qp).half ())
      else iprop("_" ∷ True))) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwait_tok, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Houtstanding Hwait_tok gives %Hle
  rw_unfold_cases
  · iNamed Houts; exfalso; omega
  · rename_i n r
    iNamed Hreaders; iNamed Hmain
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    imod own_tok_auth_delete_S γ.read_wait_gn o' $$ Houtstanding Hwait_tok with Houtstanding
    rw [if_neg (by simp only [rwmutexMaxReaders_Z] at *; word)]
    imodintro
    isplitl
    · rw_reestablish (.SignalingReaders r) pos o'
    · itrivial
  · rename_i n
    iNamed Hreaders; iNamed Hmain
    obtain ⟨o', rfl⟩ : ∃ o', o = o' + 1 := ⟨o - 1, by omega⟩
    imod own_tok_auth_delete_S γ.read_wait_gn o' $$ Houtstanding Hwait_tok with Houtstanding
    icases Hwriter with (Hwriter | ⟨_, %Hbad⟩)
    · by_cases hz : rwt + W32 (-1) = W32 0
      · rw [if_pos hz]
        icases (ghost_var_split γ.writer_sem_tok_gn () (1 : Qp).half (1 : Qp).half) $$ [Hwriter]
          with ⟨Hw1, Hw2⟩
        · rw [Qp.half_add_half]; iexact Hwriter
        imodintro
        ihave Hwriter : iprop(ghost_var γ.writer_sem_tok_gn 1 () ∨
            (ghost_var γ.writer_sem_tok_gn (1 : Qp).half () ∗
              ⌜ws = W32 0 ∧ rwt + W32 (-1) = W32 0⌝)) $$ [Hw1]
        · iright; iframe Hw1; ipureintro; simp only [rwmutexMaxReaders_Z] at *; and_intros <;> word
        isplitr [Hw2]
        · rw_reestablish .WaitingForReaders pos o'
        · iframe Hw2
      · rw [if_neg hz]
        imodintro
        isplitl
        · rw_reestablish .WaitingForReaders pos o'
        · itrivial
    · exfalso; obtain ⟨_, h⟩ := Hbad; subst h; simp only [rwmutexMaxReaders_Z] at *; word
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iexfalso; iexact Hmain
  · iNamed Houts; exfalso; omega

theorem step_rUnlockSlow_writerSem_Semrelease (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ghost_var (GF := GF) γ.writer_sem_tok_gn (1 : Qp).half () ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ("Hprot_inv" ∷ own_RWMutex_invariant γ (ws + W32 1) rs rc rwt state) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
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
    ihave Hwriter : iprop(ghost_var γ.writer_sem_tok_gn 1 () ∨
        (ghost_var γ.writer_sem_tok_gn (1 : Qp).half () ∗
          ⌜W32 0 + W32 1 = W32 0 ∧ W32 0 = W32 0⌝)) $$ [Hwriter]
    · ileft; iexact Hwriter
    rw [show (W32 0 + W32 1 : w32) = W32 1 from rfl]
    rw_reestablish .WaitingForReaders pos o

theorem step_Lock_readerCount_Add (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0)) ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> (if rc = W32 0 then
      iprop("%" ∷ ⌜state = .RLocked 0⌝ ∗
        "Hwl_inv" ∷ ghost_var γ.wlock_gn (1 : Qp).half wlock_state.IsLocked ∗
        "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 (-rwmutexMaxReaders_Z)) rwt .Locked)
    else
      iprop("Hwl" ∷ ghost_var γ.wlock_gn (1 : Qp).half
          (wlock_state.SignalingReaders (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)) ∗
        "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 (-rwmutexMaxReaders_Z)) rwt state)) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
      rw_reader_count_rel] at *
    iNamed Hreaders; iNamed Houts; iNamed Hwr; iNamed Hmain
    by_cases hz : rc = W32 0
    · rw [if_pos hz]
      imod ghost_var_update_halves wlock_state.IsLocked γ.wlock_gn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      have hn : n = 0 := by subst_vars; simp only [rwmutexMaxReaders_Z] at *; word
      subst hn
      imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish wlock_state.IsLocked pos o
    · rw [if_neg hz]
      imod ghost_var_update_halves
        (wlock_state.SignalingReaders (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z))
        γ.wlock_gn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      imodintro
      iframe Hwl_in
      rw_reestablish (wlock_state.SignalingReaders
        (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)) pos o
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

theorem step_Lock_readerWait_Add (γ : RWMutex_protocol_names) (r ws rs rc rwt : w32)
    (state : rwmutex) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half (wlock_state.SignalingReaders r) ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> (if sint.Z (rwt + r) = 0 then
      iprop("%" ∷ ⌜state = .RLocked 0⌝ ∗
        "Hwl_inv" ∷ ghost_var γ.wlock_gn (1 : Qp).half wlock_state.IsLocked ∗
        "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs rc (rwt + r) .Locked)
    else
      iprop("Hwl" ∷ ghost_var γ.wlock_gn (1 : Qp).half wlock_state.WaitingForReaders ∗
        "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs rc (rwt + r) state)) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
      rw_reader_count_rel] at *
    iNamed Hreaders; iNamed Hwr; iNamed Hmain
    by_cases hz : sint.Z (rwt + r) = 0
    · rw [if_pos hz]
      imod ghost_var_update_halves wlock_state.IsLocked γ.wlock_gn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
      have hn : n = 0 ∧ o = 0 := by simp only [rwmutexMaxReaders_Z] at *; constructor <;> word
      obtain ⟨rfl, rfl⟩ := hn
      imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish wlock_state.IsLocked pos 0
    · rw [if_neg hz]
      imod ghost_var_update_halves wlock_state.WaitingForReaders γ.wlock_gn _ _ $$ Hwl Hwl_in
        with ⟨Hwl, Hwl_in⟩
      imodintro
      iframe Hwl_in
      ihave Hwriter : iprop(ghost_var γ.writer_sem_tok_gn 1 () ∨
          (ghost_var γ.writer_sem_tok_gn (1 : Qp).half () ∗
            ⌜ws = W32 0 ∧ rwt + r = W32 0⌝)) $$ [Hwriter_unused]
      · ileft; iexact Hwriter_unused
      rw_reestablish .WaitingForReaders pos o
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

theorem step_Lock_writerSem_Semacquire (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) (Hsem : 0 < uint.Z ws) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half wlock_state.WaitingForReaders ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ("%" ∷ ⌜state = .RLocked 0⌝ ∗
      "Hwl_inv" ∷ ghost_var γ.wlock_gn (1 : Qp).half wlock_state.IsLocked ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ (ws - W32 1) rs rc rwt .Locked) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
      rw_reader_count_rel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghost_var_update_halves wlock_state.IsLocked γ.wlock_gn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    have hn : n = 0 ∧ o = 0 := by simp only [rwmutexMaxReaders_Z] at *; constructor <;> word
    obtain ⟨rfl, rfl⟩ := hn
    icases Hwriter with (Hwriter_unused | ⟨_, %Hbad⟩)
    · imodintro
      isplitr
      · ipureintro; rfl
      iframe Hwl_in
      rw_reestablish wlock_state.IsLocked pos 0
    · exfalso; obtain ⟨h, _⟩ := Hbad; subst h; simp only [rwmutexMaxReaders_Z] at *; word
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

theorem step_TryLock_readerCount_CompareAndSwap (γ : RWMutex_protocol_names) (ws rs rc rwt : w32)
    (state : rwmutex) (Hz : sint.Z rc = 0) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0)) ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ("%" ∷ ⌜state = .RLocked 0⌝ ∗
      "Hwl_inv" ∷ ghost_var γ.wlock_gn (1 : Qp).half wlock_state.IsLocked ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 (-rwmutexMaxReaders_Z)) rwt .Locked) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
      rw_reader_count_rel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghost_var_update_halves wlock_state.IsLocked γ.wlock_gn _ _ $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    have hn : n = 0 := by subst_vars; simp only [rwmutexMaxReaders_Z] at *; word
    subst hn
    imodintro
    isplitr
    · ipureintro; rfl
    iframe Hwl_in
    rw_reestablish wlock_state.IsLocked pos o
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

theorem step_Unlock_readerCount_Add (γ : RWMutex_protocol_names) (ws rs rc rwt : w32) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half wlock_state.IsLocked ∗
      own_RWMutex_invariant γ ws rs rc rwt .Locked ⊢
    |==> ("Hwl" ∷ ghost_var γ.wlock_gn (1 : Qp).half
        (wlock_state.NotLocked (rc + W32 rwmutexMaxReaders_Z)) ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws rs (rc + W32 rwmutexMaxReaders_Z) rwt (.RLocked 0) ∗
      "%" ∷ ⌜0 ≤ sint.Z (rc + W32 rwmutexMaxReaders_Z)⌝ ∗
      "%" ∷ ⌜sint.Z (rc + W32 rwmutexMaxReaders_Z) < rwmutexMaxReaders_Z⌝) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
    rw_reader_count_rel] at *
  iNamed Hmain
  imod ghost_var_update_halves (wlock_state.NotLocked (rc + W32 rwmutexMaxReaders_Z)) γ.wlock_gn _ _
    $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
  imodintro
  iframe Hwl_in
  isplitl
  · rw_reestablish (wlock_state.NotLocked (rc + W32 rwmutexMaxReaders_Z)) pos o
  · rw_pure_finish

theorem step_Unlock_readerSem_Semrelease (γ : RWMutex_protocol_names) (ws rs rc rwt r : w32)
    (state : rwmutex) (Hpos : 0 < sint.Z r) :
    ghost_var (GF := GF) γ.wlock_gn (1 : Qp).half (wlock_state.NotLocked r) ∗
      own_RWMutex_invariant γ ws rs rc rwt state ⊢
    |==> ("Hwl" ∷ ghost_var γ.wlock_gn (1 : Qp).half (wlock_state.NotLocked (r - W32 1)) ∗
      "Hprot_inv" ∷ own_RWMutex_invariant γ ws (rs + W32 1) rc rwt state) := by
  rw [own_RWMutex_invariant_unseal]; unfold own_RWMutex_invariant_def
  iintro ⟨Hwl_in, %wl, %pos, %o, Hinv⟩
  iNamed Hinv
  icombine Hwl_in Hwl gives % ⟨_, Heq⟩
  subst Heq
  cases state
  · rename_i n
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main,
      rw_reader_count_rel] at *
    iNamed Hreaders; iNamed Hmain
    imod ghost_var_update_halves (wlock_state.NotLocked (r - W32 1)) γ.wlock_gn _ _
      $$ Hwl Hwl_in with ⟨Hwl, Hwl_in⟩
    imodintro
    iframe Hwl_in
    rw_reestablish (wlock_state.NotLocked (r - W32 1)) pos o
  · simp only [rw_inv_main]
    iexfalso; iexact Hmain

end protocol

structure RWMutex_names where
  prot_gn : RWMutex_protocol_names
  reader_sem_gn : GName
  writer_sem_gn : GName

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
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

def own_RWMutex_def (γ : RWMutex_names) (state : rwmutex) : IProp GF :=
  ghost_var γ.prot_gn.state_gn (1 : Qp).half state
@[irreducible] def own_RWMutex (γ : RWMutex_names) (state : rwmutex) : IProp GF :=
  own_RWMutex_def γ state
theorem own_RWMutex_unseal : @own_RWMutex GF _ = @own_RWMutex_def GF _ := by
  funext; with_unfolding_all rfl
instance own_RWMutex_timeless (γ : RWMutex_names) (state : rwmutex) :
    Timeless (own_RWMutex (GF := GF) γ state) := by
  rw [own_RWMutex_unseal]; unfold own_RWMutex_def; infer_instance

def own_RLock_token_def (γ : RWMutex_names) : IProp GF := own_toks γ.prot_gn.rlock_overflow_gn 1
@[irreducible] def own_RLock_token (γ : RWMutex_names) : IProp GF := own_RLock_token_def γ
theorem own_RLock_token_unseal : @own_RLock_token GF _ = @own_RLock_token_def GF _ := by
  funext; with_unfolding_all rfl

abbrev RW_w (rw : loc) : loc := struct_field_ref RWMutex.t go!"w" rw
abbrev RW_readerSem (rw : loc) : loc := struct_field_ref RWMutex.t go!"readerSem" rw
abbrev RW_writerSem (rw : loc) : loc := struct_field_ref RWMutex.t go!"writerSem" rw
abbrev RW_readerCount (rw : loc) : loc := struct_field_ref RWMutex.t go!"readerCount" rw
abbrev RW_readerWait (rw : loc) : loc := struct_field_ref RWMutex.t go!"readerWait" rw

abbrev rw_locked_part (rw : loc) (γ : RWMutex_names) (state : rwmutex) : IProp GF :=
  match state with
  | .Locked => iprop(own_Mutex (RW_w (GF := GF) rw) ∗
      ghost_var γ.prot_gn.wlock_gn (1 : Qp).half wlock_state.IsLocked)
  | _ => iprop(True)

abbrev rw_inv (rw : loc) (γ : RWMutex_names) : IProp GF :=
  iprop(∃ (writer_sem reader_sem reader_count reader_wait : w32) (state : rwmutex),
    "Hstate" ∷ ghost_var γ.prot_gn.state_gn (1 : Qp).half state ∗
    "HreaderSem" ∷ own_sema γ.reader_sem_gn reader_sem ∗
    "HwriterSem" ∷ own_sema γ.writer_sem_gn writer_sem ∗
    "HreaderCount" ∷ sync.atomic.own_Int32 (RW_readerCount (GF := GF) rw) (DFrac.own 1) reader_count ∗
    "HreaderWait" ∷ sync.atomic.own_Int32 (RW_readerWait (GF := GF) rw) (DFrac.own 1) reader_wait ∗
    "Hprot" ∷ own_RWMutex_invariant γ.prot_gn writer_sem reader_sem reader_count reader_wait state ∗
    "Hlocked" ∷ rw_locked_part rw γ state)

instance rw_locked_part_timeless (rw : loc) (γ : RWMutex_names) (state : rwmutex) :
    Timeless (rw_locked_part (GF := GF) rw γ state) := by
  cases state <;> simp only [rw_locked_part] <;> infer_instance

instance rw_inv_timeless (rw : loc) (γ : RWMutex_names) : Timeless (rw_inv (GF := GF) rw γ) := by
  unfold rw_inv named; infer_instance

def is_RWMutex_def (rw : loc) (γ : RWMutex_names) (N : Namespace) : IProp GF :=
  iprop("#Hmu" ∷ is_Mutex (RW_w (GF := GF) rw)
      (ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0))) ∗
    "#His_readerSem" ∷ is_sema (RW_readerSem (GF := GF) rw) γ.reader_sem_gn (N.@"sema") ∗
    "#His_writerSem" ∷ is_sema (RW_writerSem (GF := GF) rw) γ.writer_sem_gn (N.@"sema") ∗
    "#Hinv" ∷ inv (N.@"inv") (rw_inv rw γ))
@[irreducible] def is_RWMutex (rw : loc) (γ : RWMutex_names) (N : Namespace) : IProp GF :=
  is_RWMutex_def rw γ N
theorem is_RWMutex_unseal : @is_RWMutex = @is_RWMutex_def := by funext; with_unfolding_all rfl

instance is_RWMutex_pers (rw : loc) (γ : RWMutex_names) (N : Namespace) :
    Persistent (is_RWMutex (GF := GF) rw γ N) := by
  rw [is_RWMutex_unseal]; unfold is_RWMutex_def named; infer_instance

theorem wp_RWMutex__RLock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ state, own_RWMutex γ state ∗
          (∀ num_readers, ⌜state = .RLocked num_readers⌝ →
            own_RWMutex γ (.RLocked (num_readers + 1)) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"RLock")) (Val #())) {{ Φ }} := by
  wp_start as ⟨#His, Htok⟩
  simp only [is_RWMutex_unseal, is_RWMutex_def, own_RLock_token_unseal, own_RLock_token_def]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
  imod step_RLock_readerCount_Add γ.prot_gn ws rs rc rwt state $$ [Htok Hprot] with Hprot_inv
  · iframe
  by_cases h : 0 ≤ sint.Z (rc + W32 1)
  · -- fast path
    simp only [h, ↓reduceIte]
    icases Hprot_inv with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [own_RWMutex_unseal, own_RWMutex_def]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghost_var_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, rs, (rc + W32 1), rwt, (rwmutex.RLocked (n + 1))
      simp only [rw_locked_part]
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
    wp_apply_core wp_runtime_SemacquireRWMutexR (RW_readerSem rw) γ.reader_sem_gn (N.@"sema")
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
    imod step_RLock_readerSem_Semacquire γ.prot_gn ws rs rc rwt state
      (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ Hprot with ⟨%n, %Hst, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [own_RWMutex_unseal, own_RWMutex_def]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghost_var_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ %n [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
    · inext
      iexists ws, (rs - W32 1), rc, rwt, (rwmutex.RLocked (n + 1))
      simp only [rw_locked_part]
      iframe
    imodintro
    wp_auto
    iexact HΦ

theorem wp_RWMutex__TryRLock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N ∗ own_RLock_token γ) -∗
      ▷ ((|={⊤ \ ↑N,∅}=> ∃ state, own_RWMutex γ state ∗
          (∀ num_readers, ⌜state = .RLocked num_readers⌝ →
            own_RWMutex γ (.RLocked (num_readers + 1)) ={∅,⊤ \ ↑N}=∗ Φ #true)) ∧
         Φ #false) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"TryRLock")) (Val #())) {{ Φ }} := by
  wp_start as ⟨#His, Htok⟩
  simp only [is_RWMutex_unseal, is_RWMutex_def, own_RLock_token_unseal, own_RLock_token_def]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_for
  wp_apply_core sync.atomic.wp_Int32__Load $$ [] [-]
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
  · wp_apply_core sync.atomic.wp_Int32__CompareAndSwap $$ [] [-]
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
      imod step_TryRLock_readerCount_CompareAndSwap γ.prot_gn ws rs rc' rwt state
        (by word) $$ [Htok Hprot] with ⟨%n, %Hst, Hprot⟩
      · iframe
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [own_RWMutex_unseal, own_RWMutex_def]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghost_var_update_halves (rwmutex.RLocked (n + 1)) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ %n [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hlocked] with _
      · inext
        iexists ws, rs, (rc' + W32 1), rwt, (rwmutex.RLocked (n + 1))
        simp only [rw_locked_part]
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
theorem wp_RWMutex__RUnlock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ num_readers, own_RWMutex γ (.RLocked (num_readers + 1)) ∗
          (own_RWMutex γ (.RLocked num_readers) ∗ own_RLock_token γ ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"RUnlock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [is_RWMutex_unseal, is_RWMutex_def, own_RLock_token_unseal, own_RLock_token_def]
  iNamed His
  simp only [internal.race.Enabled]
  wp_auto
  wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghost_var_update_halves (rwmutex.RLocked n) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  ihave X := step_RUnlock_readerCount_Add γ.prot_gn ws rs rc rwt n $$ Hprot
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
      simp only [rw_locked_part]
      iframe
    imodintro
    wp_auto
    have h' : sint.Z (rc + W32 (-1)) < sint.Z (W32 0) := by word
    simp only [h', decide_true]
    wp_auto
    wp_method_call
    unfold «RWMutex__rUnlockSlowⁱᵐᵖˡ»
    wp_auto
    have hA : ¬ (rc + W32 (-1) + W32 1 = W32 0) := by
      intro h; apply H1; simp only [rwmutexMaxReaders_Z] at *; word
    simp only [hA, decide_false, sync.rwmutexMaxReaders]
    wp_auto
    have hB : ¬ (rc + W32 (-1) + W32 1 = W32 (-1073741824)) := by
      intro h; apply H2; simp only [rwmutexMaxReaders_Z] at *; word
    simp only [hB, decide_false]
    wp_auto
    wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
    ihave X := step_rUnlockSlow_readerWait_Add γ.prot_gn ws rs rc2 rwt state $$ [Hwait_tok Hprot]
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
      wp_apply_core wp_runtime_Semrelease (RW_writerSem rw) γ.writer_sem_gn (N.@"sema")
        false (W64 1) $$ [] [-]
      · iframe #
      iinv Hinv with >Hi Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
      icases Hi with ⟨%ws2, %rs2, %rc3, %rwt2, %state2, Hi⟩
      iNamed Hi
      ihave Y := step_rUnlockSlow_writerSem_Semrelease γ.prot_gn ws2 rs2 rc3 rwt2 state2
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
      simp only [rw_locked_part]
      iframe
    imodintro
    wp_auto
    have h' : ¬ (sint.Z (rc + W32 (-1)) < sint.Z (W32 0)) := by word
    simp only [h', decide_false]
    wp_auto
    iexact HΦ

theorem wp_RWMutex__Lock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> ∃ state, own_RWMutex γ state ∗
          (⌜state = .RLocked 0⌝ → own_RWMutex γ .Locked ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"Lock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [is_RWMutex_unseal, is_RWMutex_def]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply wp_Mutex__Lock (RW_w rw)
    (ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0))) $$ [$Hmu]
    with ⟨Hmtx, Hwl⟩
  wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
  ihave X := step_Lock_readerCount_Add γ.prot_gn ws rs rc rwt state $$ [Hwl Hprot]
  · iframe
  imod X with X
  by_cases hz : rc = W32 0
  · -- fast path
    simp only [hz, ↓reduceIte]
    icases X with ⟨%Hst, Hwl_inv, Hprot⟩
    subst Hst
    imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
    imod HΦ with ⟨%st, Hst, HΦ⟩
    simp only [own_RWMutex_unseal, own_RWMutex_def]
    icombine Hst Hstate gives % ⟨_, heq⟩
    subst heq
    imod ghost_var_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
    imod HΦ $$ [] Hst with HΦ
    · ipureintro; rfl
    imod Hmask with _
    imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
    · inext
      iexists ws, rs, (W32 0 + W32 (-rwmutexMaxReaders_Z)), rwt, rwmutex.Locked
      simp only [rw_locked_part, named]
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
      iexists ws, rs, (rc + W32 (-rwmutexMaxReaders_Z)), rwt, state
      iframe
    imodintro
    have hz' : ¬ (rc + W32 (-1073741824) + W32 1073741824 = W32 0) := by
      intro h; apply hz; word
    wp_auto
    wp_if_destruct
    · exfalso; apply hz; word
    wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
    ihave X := step_Lock_readerWait_Add γ.prot_gn (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)
      ws rs rc' rwt state $$ [Hwl Hprot]
    · iframe
    by_cases hz2 : sint.Z (rwt + (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)) = 0
    · -- got the lock
      simp only [hz2, ↓reduceIte]
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [own_RWMutex_unseal, own_RWMutex_def]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghost_var_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)),
          rwmutex.Locked
        simp only [rw_locked_part, named]
        iframe
      imodintro
      have hz2' : rwt + (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z) = W32 0 := by
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
        iexists ws, rs, rc', (rwt + (rc + W32 (-rwmutexMaxReaders_Z) + W32 rwmutexMaxReaders_Z)), state
        iframe
      imodintro
      wp_auto
      wp_if_destruct
      · exfalso; apply hz2; rw [Hif]; rfl
      · wp_apply_core wp_runtime_SemacquireRWMutex (RW_writerSem rw) γ.writer_sem_gn (N.@"sema")
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
        ihave Y := step_Lock_writerSem_Semacquire γ.prot_gn ws rs rc rwt state
          (by simp only [uint.nat] at Hpos; simp only [uint.Z]; omega) $$ [Hwl Hprot]
        · iframe
        imod Y with ⟨%Hst, Hwl_inv, Hprot⟩
        subst Hst
        imod fupd_mask_subseteq (mask_diff_ndot2 N "sema" "inv") with Hmask
        imod HΦ with ⟨%st, Hst, HΦ⟩
        simp only [own_RWMutex_unseal, own_RWMutex_def]
        icombine Hst Hstate gives % ⟨_, heq⟩
        subst heq
        imod ghost_var_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
        imod HΦ $$ [] Hst with HΦ
        · ipureintro; rfl
        imod Hmask with _
        imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
        · inext
          iexists (ws - W32 1), rs, rc, rwt, rwmutex.Locked
          simp only [rw_locked_part, named]
          iframe
        imodintro
        wp_auto
        iexact HΦ

theorem wp_RWMutex__TryLock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N) -∗
      ▷ ((|={⊤ \ ↑N,∅}=> ∃ state, own_RWMutex γ state ∗
          (⌜state = .RLocked 0⌝ → own_RWMutex γ .Locked ={∅,⊤ \ ↑N}=∗ Φ #true)) ∧
         Φ #false) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"TryLock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [is_RWMutex_unseal, is_RWMutex_def]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply wp_Mutex__TryLock (RW_w rw)
    (ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0))) $$ [$Hmu]
    with %locked Hl
  cases locked
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    icases HΦ with ⟨-, HΦ⟩
    iexact HΦ
  · simp only [↓reduceIte]
    icases Hl with ⟨Hmtx, Hwl⟩
    wp_auto
    wp_apply_core sync.atomic.wp_Int32__CompareAndSwap $$ [] [-]
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
      ihave X := step_TryLock_readerCount_CompareAndSwap γ.prot_gn ws rs (W32 0) rwt state rfl
        $$ [Hwl Hprot]
      · iframe
      imod X with ⟨%Hst, Hwl_inv, Hprot⟩
      subst Hst
      imod Hmask with _
      icases HΦ with ⟨HΦ, -⟩
      imod fupd_mask_subseteq (mask_diff_ndot N "inv") with Hmask
      imod HΦ with ⟨%st, Hst, HΦ⟩
      simp only [own_RWMutex_unseal, own_RWMutex_def]
      icombine Hst Hstate gives % ⟨_, heq⟩
      subst heq
      imod ghost_var_update_halves rwmutex.Locked _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
      imod HΦ $$ [] Hst with HΦ
      · ipureintro; rfl
      imod Hmask with _
      have e : W32 0 + W32 (-rwmutexMaxReaders_Z) = (W32 (-1073741824) : w32) := by
        simp only [rwmutexMaxReaders_Z]; word
      rw [e]
      imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot Hmtx Hwl_inv] with _
      · inext
        iexists ws, rs, (W32 (-1073741824)), rwt, rwmutex.Locked
        simp only [rw_locked_part, named]
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
      wp_apply wp_Mutex__Unlock (RW_w rw)
        (ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0)))
        $$ [$Hmu $Hmtx $Hwl]
      icases HΦ with ⟨-, HΦ⟩
      iexact HΦ

theorem wp_RWMutex__Unlock (γ : RWMutex_names) (rw : loc) (N : Namespace) :
    ⊢ ∀ Φ : val → IProp GF,
      iprop(is_pkg_init (PROP := IProp GF) pkg_id.sync ∗ is_RWMutex rw γ N) -∗
      ▷ (|={⊤ \ ↑N,∅}=> own_RWMutex γ .Locked ∗
          (own_RWMutex γ (.RLocked 0) ={∅,⊤ \ ↑N}=∗ Φ #())) -∗
      WP (App (Val (rw @!! go.type.PointerType RWMutex @!! go!"Unlock")) (Val #())) {{ Φ }} := by
  wp_start as #His
  simp only [is_RWMutex_unseal, is_RWMutex_def]
  iNamed His
  simp only [internal.race.Enabled, sync.rwmutexMaxReaders]
  wp_auto
  wp_apply_core sync.atomic.wp_Int32__Add $$ [] [-]
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
  simp only [own_RWMutex_unseal, own_RWMutex_def]
  icombine Hst Hstate gives % ⟨_, heq⟩
  subst heq
  imod ghost_var_update_halves (rwmutex.RLocked 0) _ _ _ $$ Hst Hstate with ⟨Hst, Hstate⟩
  imod HΦ $$ Hst with HΦ
  imod Hmask with -
  simp only [rw_locked_part]
  icases Hlocked with ⟨Hmtx, Hwl_in⟩
  ihave X := step_Unlock_readerCount_Add γ.prot_gn ws rs rc rwt $$ [Hwl_in Hprot]
  · iframe
  imod X with ⟨Hwl, Hprot, %Hr1, %Hr2⟩
  imod Hclose $$ [Hstate HreaderSem HwriterSem HreaderCount HreaderWait Hprot] with -
  · inext
    iexists ws, rs, (rc + W32 rwmutexMaxReaders_Z), rwt, (rwmutex.RLocked 0)
    simp only [rw_locked_part]
    iframe
  imodintro
  wp_auto
  wp_if_destruct
  · exfalso; simp only [rwmutexMaxReaders_Z] at *; word
  ihave HI : iprop(∃ (i : w64) (r2 : w32), "i" ∷ i_ptr ↦ i ∗
      "Hwl" ∷ ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked r2) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (rc + W32 rwmutexMaxReaders_Z)⌝ ∗
      "%Hrr" ∷ ⌜sint.Z r2 = sint.Z (rc + W32 rwmutexMaxReaders_Z) - sint.Z i⌝) $$ [i Hwl]
  · iexists (W64 0), (rc + W32 rwmutexMaxReaders_Z)
    iframe
    ipureintro; simp only [rwmutexMaxReaders_Z] at *; and_intros <;> word
  wp_for HI
  split
  · rename_i hlt
    simp only [decide_eq_true_eq, sext_32_64] at hlt
    wp_auto
    wp_apply_core wp_runtime_Semrelease (RW_readerSem rw) γ.reader_sem_gn (N.@"sema")
      false (W64 0) $$ [] [-]
    · iframe #
    have hpos : 0 < sint.Z r2 := by simp only [rwmutexMaxReaders_Z] at *; word
    have hfin : (0 ≤ sint.Z (i + W64 1) ∧ sint.Z (i + W64 1) ≤ sint.Z (rc + W32 rwmutexMaxReaders_Z)) ∧
        sint.Z (r2 - W32 1) = sint.Z (rc + W32 rwmutexMaxReaders_Z) - sint.Z (i + W64 1) := by
      simp only [rwmutexMaxReaders_Z] at *; and_intros <;> word
    clear Hif hlt Hr1 Hr2 Hi Hrr
    iinv Hinv with >Hi2 Hclose <;> try exact ⟨mask_inv_sema N, trivial⟩
    icases Hi2 with ⟨%ws, %rs, %rc', %rwt, %state, Hi2⟩
    iNamed Hi2
    ihave X := step_Unlock_readerSem_Semrelease γ.prot_gn ws rs rc' rwt r2 state hpos $$ [Hwl Hprot]
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
    have hr0 : r2 = W32 0 := by simp only [rwmutexMaxReaders_Z] at *; word
    subst hr0
    wp_auto
    wp_apply wp_Mutex__Unlock (RW_w rw)
      (ghost_var γ.prot_gn.wlock_gn (1 : Qp).half (wlock_state.NotLocked (W32 0)))
      $$ [$Hmu $Hmtx $Hwl]
    iexact HΦ

theorem own_toks_replicate (γ : GName) (n : Nat) :
    own_toks (GF := GF) γ n ⊢ [∗list] _x ∈ List.replicate n (), own_toks γ 1 := by
  induction n with
  | zero => simp only [List.replicate]; exact BigSepL.bigSepL_nil_intro
  | succ n ih =>
    iintro H
    simp only [List.replicate]
    iapply BigSepL.bigSepL_cons.2
    icases (own_toks_add n 1 γ).1 $$ [H] with ⟨H1, H2⟩
    · rw [Nat.add_comm]; iexact H
    iframe H1
    iapply ih $$ H2

theorem init_RWMutex {E : CoPset} (N : Namespace) (rw : loc) :
    typed_pointsto (GF := GF) rw (zero_val RWMutex.t) (DFrac.own 1) ⊢
    |={E}=> ∃ γ : RWMutex_names, is_RWMutex rw γ N ∗ own_RWMutex γ (.RLocked 0) ∗
      [∗list] _x ∈ List.replicate (Int.toNat actualMaxReaders) (), own_RLock_token γ := by
  iintro Hrw
  iStructNamed Hrw
  rw [show (zero_val RWMutex.t).readerSem' = W32 0 from rfl,
    show (zero_val RWMutex.t).writerSem' = W32 0 from rfl,
    show (zero_val RWMutex.t).readerCount' =
      ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32.t) from rfl,
    show (zero_val RWMutex.t).readerWait' =
      ({ _0' := zero_val _, v' := W32 0 } : sync.atomic.Int32.t) from rfl]
  imod own_tok_auth_alloc (GF := GF) with ⟨%γread_wait, Hread_wait⟩
  imod own_tok_auth_alloc (GF := GF) with ⟨%γrlock, Hrlock⟩
  imod own_tok_auth_add (Int.toNat actualMaxReaders) γrlock 0 $$ Hrlock with ⟨Hrlock, Htoks⟩
  imod ghost_var_alloc (wlock_state.NotLocked (W32 0)) with ⟨%γwl, Hwl⟩
  icases ghost_var_split γwl (wlock_state.NotLocked (W32 0)) (1 : Qp).half (1 : Qp).half $$ [Hwl]
    with ⟨Hwl, Hwl_inv⟩
  · rw [Qp.half_add_half]; iexact Hwl
  imod ghost_var_alloc (rwmutex.RLocked 0) with ⟨%γst, Hst⟩
  icases ghost_var_split γst (rwmutex.RLocked 0) (1 : Qp).half (1 : Qp).half $$ [Hst]
    with ⟨Hst, Hst_inv⟩
  · rw [Qp.half_add_half]; iexact Hst
  imod ghost_var_alloc () with ⟨%γwt, Hwt⟩
  imod init_sema (E := E) (N.@"sema") (RW_readerSem rw) (W32 0) $$ readerSem with ⟨%γrs, #Hrs, Hrs_own⟩
  imod init_sema (E := E) (N.@"sema") (RW_writerSem rw) (W32 0) $$ writerSem with ⟨%γws, #Hws, Hws_own⟩
  let γ : RWMutex_names := ⟨⟨γread_wait, γrlock, γwl, γwt, γst⟩, γrs, γws⟩
  imod init_Mutex (ghost_var γwl (1 : Qp).half (wlock_state.NotLocked (W32 0))) E (RW_w rw)
    $$ w [Hwl] with #Hmu
  · inext; iexact Hwl
  imod own_toks_0 (GF := GF) γrlock with H0
  ihave Hprot : own_RWMutex_invariant (GF := GF) γ.prot_gn (W32 0) (W32 0) (W32 0) (W32 0)
      (rwmutex.RLocked 0) $$ [Hread_wait Hwl_inv Hrlock H0 Hwt]
  · simp only [own_RWMutex_invariant_unseal, own_RWMutex_invariant_def]
    iexists (wlock_state.NotLocked (W32 0)), (W32 0), 0
    simp only [rw_inv_readers, rw_inv_outstanding, rw_inv_writer, rw_inv_main, rw_reader_count_rel,
      Nat.zero_add, show (sint.Z (W32 0)).toNat = 0 from rfl]
    iframe
    simp only [named]
    ipureintro
    simp only [rwmutexMaxReaders_Z]
    and_intros <;> word
  imod inv_alloc (N.@"inv") E (rw_inv rw γ) $$ [Hst_inv Hrs_own Hws_own readerCount readerWait
      Hprot] with #Hinv
  · inext
    iexists (W32 0), (W32 0), (W32 0), (W32 0), (rwmutex.RLocked 0)
    simp only [rw_locked_part, sync.atomic.own_Int32_unseal, sync.atomic.own_Int32_def]
    iframe
  imodintro
  iexists γ
  simp only [is_RWMutex_unseal, is_RWMutex_def, own_RWMutex_unseal, own_RWMutex_def,
    own_RLock_token_unseal, own_RLock_token_def]
  iframe Hst
  iframe #
  iapply own_toks_replicate $$ Htoks

end wps

end rwmutex

end sync

end Perennial
end
