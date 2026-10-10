/-
Thread tokens: the ghost-state side of the thread bound of the bounded semantics
(`BoundedLang.lean`, thread fuel).

* `threadTok`: one exclusive thread token, "a live thread".
* `threadToks n`: `n` of them.

The bound `T = threadBound GF` is not fixed: it is chosen when the ghost state
is allocated by the adequacy theorem (`goose_adequacy N T`, `Adequacy.lean`),
where it is also the bound on the number of live threads
(`GlobalState.threads`) of the real executions the theorem is about. The laws
are stated for this abstract bound; a proof that needs it to be small takes a
premise such as `threadBound GF ≤ 2 ^ 31`.

`threadToks n ⊢ ⌜n < T⌝`, so `threadToks T ⊢ False`: `n` tokens are `n`
distinct slots below `T - 1`.

Accounting. There are `T - 1` tokens in total (the slots `0, ..., T - 2`). One
is held by the main thread for the whole execution (the adequacy theorem hands
it to the program); the others are the *thread fuel* of the bounded semantics,
owned by the GooseLang state interpretation (`threadFuel t = threadToks t`,
`Lifting.lean`). `Fork` takes one token out of the fuel and hands it to the
forking thread (`wp_fork_tok`), and the forked thread `e ;; ThreadExit` returns
one at its `ThreadExit` (`wp_ThreadExit`). In between, the token may be held by
any thread or invariant: e.g. a `sync.WaitGroup`'s invariant can hold one per
goroutine that has been `Add`ed and not yet `Done`, so that its counter, backed
by that many tokens, is below `T`. Since every live thread is accounted for by
exactly one token, this is the argument "`T` goroutines cannot be live at the
same time" made inside the logic.

The tokens are built from a `ghost_map Nat Unit` (`threadTokName`): the token
of slot `k` is `k ↪ ()` together with `⌜k + 1 < T⌝`. Tokens are exclusive, so
the `n` tokens of `threadToks n` are `n` distinct slots below `T - 1`, whence
`n ≤ T - 1` *without* access to an authoritative part: the authoritative map
is allocated with all `T - 1` slots and discarded (`thread_init`).

`ThreadGS` carries its own `allG GF` (`threadAllG`), a local instance of this
file only, for the same reason as `receiptAllG` (`Receipts.lean`).
-/
module

public import Iris.Instances.IProp
public import Iris.ProofMode
public import Perennial.Ghost.GhostMap
public import Perennial.GooseLang.Receipts

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

/-- Ghost state for thread tokens, before allocation. It does not fix the bound,
which is chosen when the ghost state is allocated (`thread_init`). -/
class ThreadGpreS (GF : BundledGFunctors) where
  threadPreGAllG : AllG GF

/-- Ghost state for thread tokens. `threadBound` is the bound `T` on the number
of live threads (`threadToks T ⊢ False`): an unspecified number above `1` (the
main thread is live), fixed when the ghost state is allocated at adequacy time
(`goose_adequacy`), where it also bounds `GlobalState.threads` along the
executions the theorem is about. A proof that needs `T` to be small enough takes
it as a premise (e.g. `threadBound GF ≤ 2 ^ 31`). -/
class ThreadGS (GF : BundledGFunctors) where
  threadAllG : AllG GF
  /-- `ghost_map Nat Unit`: the token `k ↪ ()` of every thread slot `k < T - 1`. -/
  threadTokName : GName
  threadBound : Nat
  threadBound_gt : 1 < threadBound

attribute [reducible] ThreadGS.threadAllG
attribute [local instance] ThreadGS.threadAllG

export ThreadGS (threadBound threadBound_gt)

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [hT : ThreadGS GF]

/-- The tokens of the slots `ks`: each slot's token, and that it is below `T - 1`. -/
def threadTokList : List Nat → IProp GF
  | [] => iprop(emp)
  | k :: ks => iprop(⌜k + 1 < hT.threadBound⌝ ∗ (k ↪[hT.threadTokName] ()) ∗ threadTokList ks)

/-- `threadToks n`: `n` exclusive thread tokens. -/
def threadToks (n : Nat) : IProp GF :=
  iprop(∃ ks : List Nat, ⌜ks.length = n⌝ ∗ threadTokList ks)

/-- One thread token: a live thread. -/
abbrev threadTok : IProp GF := threadToks 1

/-- The thread part of the state interpretation of the bounded language, for
thread fuel `t`: the `t` tokens of the threads that may still be forked
(`Lifting.lean`). -/
def threadFuel (t : Nat) : IProp GF := threadToks t

end defs

/-! ## Laws -/

section laws
variable {GF : BundledGFunctors} [hT : ThreadGS GF]
open ProofMode

instance threadTokList_timeless (ks : List Nat) : Timeless (threadTokList (GF := GF) ks) := by
  induction ks with
  | nil => unfold threadTokList; infer_instance
  | cons k ks ih => unfold threadTokList; infer_instance

instance threadToks_timeless (n : Nat) : Timeless (threadToks (GF := GF) n) := by
  unfold threadToks; infer_instance

instance threadFuel_timeless (t : Nat) : Timeless (threadFuel (GF := GF) t) := by
  unfold threadFuel; infer_instance

theorem threadTokList_append (ks1 ks2 : List Nat) :
    threadTokList (GF := GF) (ks1 ++ ks2) ⊣⊢ threadTokList ks1 ∗ threadTokList ks2 := by
  induction ks1 with
  | nil => exact emp_sep.symm
  | cons k ks ih =>
    show iprop(_ ∗ _ ∗ threadTokList (ks ++ ks2)) ⊣⊢ iprop((_ ∗ _ ∗ threadTokList ks) ∗ _)
    exact (sep_congr .rfl (sep_congr .rfl ih)).trans
      ((sep_congr .rfl sep_assoc.symm).trans sep_assoc.symm)

/-- A token is not among the tokens of `ks`. -/
theorem threadTokList_not_mem (k : Nat) (ks : List Nat) :
    (k ↪[hT.threadTokName] ()) ∗ threadTokList (GF := GF) ks ⊢ ⌜k ∉ ks⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k' ks ih =>
    unfold threadTokList
    iintro ⟨Hk, -, Hk', Hks⟩
    icases ghostMapElem_ne _ k k' _ () () $$ Hk Hk' with %Hne
    ihave %Hnot := ih $$ [Hk Hks]
    · iframe
    ipureintro
    simp only [List.mem_cons, not_or]
    exact ⟨Hne, Hnot⟩

/-- The slots of `ks` are distinct and below `T - 1`. -/
theorem threadTokList_nodup (ks : List Nat) :
    threadTokList (GF := GF) ks ⊢ ⌜ks.Nodup ∧ ∀ k ∈ ks, k + 1 < hT.threadBound⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k ks ih =>
    unfold threadTokList
    iintro ⟨%Hlt, Hk, Hks⟩
    icases threadTokList_not_mem k ks $$ [Hk Hks] with %Hnot
    · iframe
    icases ih $$ Hks with %⟨Hnd, Hall⟩
    ipureintro
    refine ⟨List.nodup_cons.mpr ⟨Hnot, Hnd⟩, fun k' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | h
    · exact Hlt
    · exact Hall k' h

/-- `threadToks (m + n) ⊣⊢ threadToks m ∗ threadToks n`. -/
theorem threadToks_add (m n : Nat) :
    threadToks (GF := GF) (m + n) ⊣⊢ threadToks m ∗ threadToks n := by
  unfold threadToks
  constructor
  · iintro ⟨%ks, %Hlen, Hks⟩
    rw [← List.take_append_drop m ks]
    icases (threadTokList_append (GF := GF) _ _).1 $$ Hks with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ks.take m; iframe H1; ipureintro; simp [Hlen]
    · iexists ks.drop m; iframe H2; ipureintro; simp [Hlen]
  · iintro ⟨⟨%ks1, %H1, Hks1⟩, ⟨%ks2, %H2, Hks2⟩⟩
    iexists ks1 ++ ks2
    isplitr
    · ipureintro; simp [H1, H2]
    · iapply (threadTokList_append (GF := GF) _ _).2; iframe

/-- `True ⊢ threadToks 0`. -/
theorem threadToks_zero : ⊢ threadToks (GF := GF) 0 := by
  unfold threadToks
  iexists []
  isplitr
  · ipureintro; rfl
  · unfold threadTokList; iempintro

/-- `n` tokens: `n < T`. -/
theorem threadToks_lt (n : Nat) : threadToks (GF := GF) n ⊢ ⌜n < hT.threadBound⌝ := by
  unfold threadToks
  iintro ⟨%ks, %Hlen, Hks⟩
  icases threadTokList_nodup ks $$ Hks with %⟨Hnd, Hall⟩
  ipureintro
  have := hT.threadBound_gt
  have := length_le_of_nodup_lt (b := hT.threadBound - 1) Hnd fun k hk => by
    have := Hall k hk; omega
  omega

/-- `threadToks T ⊢ False`: `threadBound` thread tokens are contradictory. -/
theorem threadBound_elim : threadToks (GF := GF) hT.threadBound ⊢ False := by
  refine (threadToks_lt _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- The form with a mask, `threadToks T ={E}=∗ False`. -/
theorem threadBound_fupd [FUpd (IProp GF)] (E : CoPset) :
    threadToks (GF := GF) hT.threadBound ⊢ |={E}=> False :=
  threadBound_elim.trans false_elim

/-- One more token joining `n` tokens: `n + 1 < T`. -/
theorem threadToks_add_one_lt (n : Nat) :
    threadTok ∗ threadToks (GF := GF) n ⊢ ⌜n + 1 < hT.threadBound⌝ ∗ threadToks (n + 1) := by
  refine sep_comm.1.trans ((threadToks_add n 1).2.trans ?_)
  exact (persistent_entails_left (threadToks_lt (n + 1))).trans sep_comm.1

/-! ### The thread fuel -/

/-- `Fork` with thread fuel `t + 1`: one token out of the fuel. -/
theorem threadFuel_fork (t : Nat) :
    threadFuel (GF := GF) (t + 1) ⊢ threadFuel t ∗ threadTok :=
  (threadToks_add t 1).1

/-- `ThreadExit` with thread fuel `t`: the thread's token back into the fuel. -/
theorem threadFuel_exit (t : Nat) :
    threadFuel (GF := GF) t ∗ threadTok ⊢ threadFuel (t + 1) :=
  (threadToks_add t 1).2

end laws

/-! ## Allocation -/

section init
variable {GF : BundledGFunctors} [hPre : ThreadGpreS GF]
open ProofMode

/-- The slots `0, ..., n - 1` of the ghost map `γ` allocated, as `n` tokens, with the
other slots free. -/
private theorem thread_init_aux (T : Nat) (hT : 1 < T) (γ : GName) (n : Nat) (hn : n ≤ T - 1) :
    (letI := hPre.threadPreGAllG; ghostMapAuth γ 1 (∅ : GMap Nat Unit)) ⊢@{IProp GF}
      |==> ∃ m : GMap Nat Unit,
        (letI := hPre.threadPreGAllG; ghostMapAuth γ 1 m) ∗
        ⌜∀ k, n ≤ k → m.lookup k = none⌝ ∗
        threadToks (hT := ⟨hPre.threadPreGAllG, γ, T, hT⟩) n := by
  letI := hPre.threadPreGAllG
  induction n with
  | zero =>
    iintro Hm
    imodintro
    iexists ∅
    iframe Hm
    isplitr
    · ipureintro; intro k _; rfl
    · exact threadToks_zero (hT := ⟨hPre.threadPreGAllG, γ, T, hT⟩)
  | succ n ih =>
    iintro Hm
    imod ih (by omega) $$ Hm with ⟨%m, Hm, %Hfree, Htoks⟩
    imod ghost_map_insert n () (Hfree n (Nat.le_refl n)) $$ Hm with ⟨Hm, Htok⟩
    imodintro
    iexists (<[n := ()]> m)
    iframe Hm
    isplitr
    · ipureintro
      intro k hk
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      exact Hfree k (by omega)
    · iapply (threadToks_add (hT := ⟨hPre.threadPreGAllG, γ, T, hT⟩) n 1).2
      iframe Htoks
      unfold threadToks
      iexists [n]
      isplitr
      · ipureintro; rfl
      · unfold threadTokList threadTokList
        iframe Htok
        ipureintro
        show n + 1 < T
        omega

/-- Allocation of the thread ghost state for a bound `T > 1`: all `T - 1` tokens.
The adequacy theorem hands one to the main thread and makes the others the
initial thread fuel of the bounded semantics. -/
theorem thread_init (T : Nat) (hT : 1 < T) :
    ⊢@{IProp GF} |==> ∃ γ : GName, threadToks (hT := ⟨hPre.threadPreGAllG, γ, T, hT⟩) (T - 1) := by
  letI := hPre.threadPreGAllG
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γ, Hm⟩
  imod thread_init_aux T hT γ (T - 1) (Nat.le_refl _) $$ Hm with ⟨%m, -, -, Htoks⟩
  imodintro
  iexists γ
  iexact Htoks

end init

end Perennial
