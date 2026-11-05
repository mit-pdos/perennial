/-
Thread tokens: the ghost-state side of the thread bound of the bounded semantics
(`BoundedLang.lean`, thread fuel).

* `threadTok`: one exclusive thread token, "a live thread".
* `threadToks n`: `n` of them.
* `levelTok l`, `levelToks l n`: the token of one **level** `l < T`; `threadTokFrom l`: the
  levels `l` to `T - 1` of one thread token.

The bound `T = threadBound GF` is not fixed: it is chosen when the ghost state
is allocated by the adequacy theorem (`goose_adequacy N T`, `Adequacy.lean`),
where it is also the bound on the number of live threads
(`state.threads`) of the real executions the theorem is about. The laws
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

Levels. A thread token is one token of each of `T` levels (`threadTok_bigSepL`,
`threadTokFrom_succ`: `threadTokFrom l ⊣⊢ levelTok l ∗ threadTokFrom (l + 1)` for `l < T`), and
each level has its own `T - 1` tokens (`levelToks l n ⊢ ⌜n < T⌝`). A thread may hand some levels
of its token to others and keep the rest: e.g. a goroutine of a leveled wait group
(`sync.tokJoinL`) runs with its levels from `1` while the group holds its level `0`, and borrows
from a thread pool at a level it holds (`threadPool.isThreadPoolL`). The levels of
`threadToks n` need not be of the same slots. The fuel and `ThreadExit` still trade whole tokens,
and `n` whole tokens contain `n` level-`0` tokens, so they are still fewer than `T`, however they
were assembled.

The tokens are built from a `ghost_map Nat Unit` (`threadTokName`): the token
of slot `k` at level `l` is `levelKey l k ↪ ()` (the key `l * T + k`) together with
`⌜k + 1 < T⌝`. Tokens are exclusive, so the `n` tokens of `levelToks l n` are `n`
distinct slots below `T - 1`, whence `n ≤ T - 1` *without* access to an
authoritative part: the authoritative map is allocated with all `T - 1` slots of
every level and discarded (`thread_init`).

The tokens are ghost state of the one `allG GF`, which `GooseGlobalGS`
(`Lifting.lean`) carries; here it is the ambient `[AllG GF]`. `ThreadGS` is
per generation (a field of `GooseLocalGS`): a crash kills every thread, and the
next generation gets new tokens (`goose_crash_step`, `CrashAdequacy.lean`).
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

/-- Ghost state for thread tokens. `threadBound` is the bound `T` on the number
of live threads (`threadToks T ⊢ False`): an unspecified number above `1` (the
main thread is live), fixed when the ghost state is allocated at adequacy time
(`goose_adequacy`), where it also bounds `state.threads` along the
executions the theorem is about. A proof that needs `T` to be small enough takes
it as a premise (e.g. `threadBound GF ≤ 2 ^ 31`). The names are those of ghost
state of the ambient `[AllG GF]`; before allocation (`thread_init`) nothing but
`AllG GF` is needed. -/
class ThreadGS (GF : BundledGFunctors) where
  /-- `ghost_map Nat Unit`: the token `l * T + k ↪ ()` of every thread slot `k < T - 1` at every
  level `l < T` (`levelKey`). -/
  threadTokName : GName
  threadBound : Nat
  threadBound_gt : 1 < threadBound

export ThreadGS (threadBound threadBound_gt)

/-! ## Definitions -/

section defs
variable {GF : BundledGFunctors} [AllG GF] [hT : ThreadGS GF]

/-- The ghost-map key of the token of slot `k` at level `l`: `l * T + k`. The slots are below
`T - 1`, so different (slot, level) pairs have different keys. -/
def levelKey (l k : Nat) : Nat := l * hT.threadBound + k

/-- The tokens of the slots `ks` at level `0`: each slot's token, and that it is below `T - 1`.
Kept, with its laws, from before the levels: it is `levelTokList 0` (`threadTokList_level0`), and
nothing is built from it; use `levelTokList`. -/
def threadTokList : List Nat → IProp GF
  | [] => iprop(emp)
  | k :: ks => iprop(⌜k + 1 < hT.threadBound⌝ ∗ (k ↪[hT.threadTokName] ()) ∗ threadTokList ks)

/-- The level-`l` tokens of the slots `ks`: each one's token, and that the slot is below `T - 1`. -/
def levelTokList (l : Nat) : List Nat → IProp GF
  | [] => iprop(emp)
  | k :: ks =>
    iprop(⌜k + 1 < hT.threadBound⌝ ∗ (levelKey (GF := GF) l k ↪[hT.threadTokName] ()) ∗
      levelTokList l ks)

/-- `levelToks l n`: `n` exclusive tokens of level `l`, of `n` distinct slots. -/
def levelToks (l n : Nat) : IProp GF :=
  iprop(∃ ks : List Nat, ⌜ks.length = n⌝ ∗ levelTokList l ks)

/-- One token of level `l`. -/
abbrev levelTok (l : Nat) : IProp GF := levelToks l 1

/-- `levelsToks l c n`: `n` tokens of each of the `c` levels `l, ..., l + c - 1`. -/
def levelsToks : Nat → Nat → Nat → IProp GF
  | _, 0, _ => iprop(emp)
  | l, c + 1, n => iprop(levelToks l n ∗ levelsToks (l + 1) c n)

/-- `threadToksFrom l n`: `n` tokens of each level from `l` to `T - 1`, the levels of `n` thread
tokens but the ones below `l`. -/
def threadToksFrom (l n : Nat) : IProp GF := levelsToks l (hT.threadBound - l) n

/-- The levels `l` to `T - 1` of one thread token. -/
abbrev threadTokFrom (l : Nat) : IProp GF := threadToksFrom l 1

/-- `threadToks n`: `n` exclusive thread tokens, that is `n` tokens of each of the `T` levels
(`threadToks_bigSepL`). -/
def threadToks (n : Nat) : IProp GF := threadToksFrom 0 n

/-- One thread token: a live thread. -/
abbrev threadTok : IProp GF := threadToks 1

/-- The thread part of the state interpretation of the bounded language, for
thread fuel `t`: the `t` tokens of the threads that may still be forked
(`Lifting.lean`). -/
def threadFuel (t : Nat) : IProp GF := threadToks t

end defs

/-! ## Laws -/

section laws
variable {GF : BundledGFunctors} [AllG GF] [hT : ThreadGS GF]
open ProofMode

instance threadTokList_timeless (ks : List Nat) : Timeless (threadTokList (GF := GF) ks) := by
  induction ks with
  | nil => unfold threadTokList; infer_instance
  | cons k ks ih => unfold threadTokList; infer_instance

instance levelTokList_timeless (l : Nat) (ks : List Nat) :
    Timeless (levelTokList (GF := GF) l ks) := by
  induction ks with
  | nil => unfold levelTokList; infer_instance
  | cons k ks ih => unfold levelTokList; infer_instance

instance levelToks_timeless (l n : Nat) : Timeless (levelToks (GF := GF) l n) := by
  unfold levelToks; infer_instance

instance levelsToks_timeless (l c n : Nat) : Timeless (levelsToks (GF := GF) l c n) := by
  induction c generalizing l with
  | zero => unfold levelsToks; infer_instance
  | succ c ih => unfold levelsToks; infer_instance

instance threadToksFrom_timeless (l n : Nat) : Timeless (threadToksFrom (GF := GF) l n) := by
  unfold threadToksFrom; infer_instance

instance threadToks_timeless (n : Nat) : Timeless (threadToks (GF := GF) n) := by
  unfold threadToks; infer_instance

instance threadFuel_timeless (t : Nat) : Timeless (threadFuel (GF := GF) t) := by
  unfold threadFuel; infer_instance

/-! ### The tokens of one level -/

theorem threadTokList_append (ks1 ks2 : List Nat) :
    threadTokList (GF := GF) (ks1 ++ ks2) ⊣⊢ threadTokList ks1 ∗ threadTokList ks2 := by
  induction ks1 with
  | nil => exact emp_sep.symm
  | cons k ks ih =>
    show iprop(_ ∗ _ ∗ threadTokList (ks ++ ks2)) ⊣⊢ iprop((_ ∗ _ ∗ threadTokList ks) ∗ _)
    exact (sep_congr .rfl (sep_congr .rfl ih)).trans
      ((sep_congr .rfl sep_assoc.symm).trans sep_assoc.symm)

theorem levelTokList_append (l : Nat) (ks1 ks2 : List Nat) :
    levelTokList (GF := GF) l (ks1 ++ ks2) ⊣⊢ levelTokList l ks1 ∗ levelTokList l ks2 := by
  induction ks1 with
  | nil => exact emp_sep.symm
  | cons k ks ih =>
    show iprop(_ ∗ _ ∗ levelTokList l (ks ++ ks2)) ⊣⊢
      iprop((_ ∗ _ ∗ levelTokList l ks) ∗ _)
    exact (sep_congr .rfl (sep_congr .rfl ih)).trans
      ((sep_congr .rfl sep_assoc.symm).trans sep_assoc.symm)

/-- The tokens of `threadTokList` are those of level `0`. -/
theorem threadTokList_level0 (ks : List Nat) :
    threadTokList (GF := GF) ks ⊣⊢ levelTokList 0 ks := by
  induction ks with
  | nil => exact .rfl
  | cons k ks ih =>
    have hk : levelKey (GF := GF) 0 k = k := by simp [levelKey]
    simp only [threadTokList, levelTokList, hk]
    exact sep_congr .rfl (sep_congr .rfl ih)

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

/-- A level-`l` token is not among the level-`l` tokens of `ks`. -/
theorem levelTokList_not_mem (l k : Nat) (ks : List Nat) :
    (levelKey (GF := GF) l k ↪[hT.threadTokName] ()) ∗ levelTokList (GF := GF) l ks ⊢
      ⌜k ∉ ks⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k' ks ih =>
    unfold levelTokList
    iintro ⟨Hk, -, Hk', Hks⟩
    icases ghostMapElem_ne _ (levelKey (GF := GF) l k) (levelKey (GF := GF) l k') _ () ()
      $$ Hk Hk' with %Hne
    ihave %Hnot := ih $$ [Hk Hks]
    · iframe
    ipureintro
    simp only [List.mem_cons, not_or]
    exact ⟨fun h => Hne (by rw [h]), Hnot⟩

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

/-- The slots of the level-`l` tokens `ks` are distinct and below `T - 1`. -/
theorem levelTokList_nodup (l : Nat) (ks : List Nat) :
    levelTokList (GF := GF) l ks ⊢ ⌜ks.Nodup ∧ ∀ k ∈ ks, k + 1 < hT.threadBound⌝ := by
  induction ks with
  | nil => iintro -; ipureintro; simp
  | cons k ks ih =>
    unfold levelTokList
    iintro ⟨%Hlt, Hk, Hks⟩
    icases levelTokList_not_mem l k ks $$ [Hk Hks] with %Hnot
    · iframe
    icases ih $$ Hks with %⟨Hnd, Hall⟩
    ipureintro
    refine ⟨List.nodup_cons.mpr ⟨Hnot, Hnd⟩, fun k' hk' => ?_⟩
    rcases List.mem_cons.mp hk' with rfl | h
    · exact Hlt
    · exact Hall k' h

/-- `levelToks l (m + n) ⊣⊢ levelToks l m ∗ levelToks l n`. -/
theorem levelToks_add (l m n : Nat) :
    levelToks (GF := GF) l (m + n) ⊣⊢ levelToks l m ∗ levelToks l n := by
  unfold levelToks
  constructor
  · iintro ⟨%ks, %Hlen, Hks⟩
    rw [← List.take_append_drop m ks]
    icases (levelTokList_append (GF := GF) l _ _).1 $$ Hks with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ks.take m; iframe H1; ipureintro; simp [Hlen]
    · iexists ks.drop m; iframe H2; ipureintro; simp [Hlen]
  · iintro ⟨⟨%ks1, %H1, Hks1⟩, ⟨%ks2, %H2, Hks2⟩⟩
    iexists ks1 ++ ks2
    isplitr
    · ipureintro; simp [H1, H2]
    · iapply (levelTokList_append (GF := GF) l _ _).2; iframe

/-- `True ⊢ levelToks l 0`. -/
theorem levelToks_zero (l : Nat) : ⊢ levelToks (GF := GF) l 0 := by
  unfold levelToks
  iexists []
  isplitr
  · ipureintro; rfl
  · unfold levelTokList; iempintro

/-- `n` tokens of one level: `n < T`. Each level has its own `T - 1` slots. -/
theorem levelToks_lt (l n : Nat) : levelToks (GF := GF) l n ⊢ ⌜n < hT.threadBound⌝ := by
  unfold levelToks
  iintro ⟨%ks, %Hlen, Hks⟩
  icases levelTokList_nodup l ks $$ Hks with %⟨Hnd, Hall⟩
  ipureintro
  have := hT.threadBound_gt
  have := length_le_of_nodup_lt (b := hT.threadBound - 1) Hnd fun k hk => by
    have := Hall k hk; omega
  omega

/-- `levelToks l T ⊢ False`. -/
theorem levelBound_elim (l : Nat) : levelToks (GF := GF) l hT.threadBound ⊢ False := by
  refine (levelToks_lt l _).trans ?_
  iintro %H
  exact absurd H (Nat.lt_irrefl _)

/-- One more level-`l` token joining `n` of them: `n + 1 < T`. -/
theorem levelToks_add_one_lt (l n : Nat) :
    levelTok l ∗ levelToks (GF := GF) l n ⊢
      ⌜n + 1 < hT.threadBound⌝ ∗ levelToks l (n + 1) := by
  refine sep_comm.1.trans ((levelToks_add l n 1).2.trans ?_)
  exact (persistent_entails_left (levelToks_lt l (n + 1))).trans sep_comm.1

/-! ### Several levels -/

theorem levelsToks_add (l c m n : Nat) :
    levelsToks (GF := GF) l c (m + n) ⊣⊢ levelsToks l c m ∗ levelsToks l c n := by
  induction c generalizing l with
  | zero => exact emp_sep.symm
  | succ c ih =>
    simp only [levelsToks]
    exact (sep_congr (levelToks_add l m n) (ih (l + 1))).trans sep_sep_sep_comm

theorem levelsToks_zero (l c : Nat) : ⊢ levelsToks (GF := GF) l c 0 := by
  induction c generalizing l with
  | zero => exact .rfl
  | succ c ih =>
    simp only [levelsToks]
    exact sep_emp.2.trans (sep_mono (levelToks_zero l) (ih (l + 1)))

theorem levelsToks_bigSepL (l c n : Nat) :
    levelsToks (GF := GF) l c n ⊣⊢ [∗list] l' ∈ List.range' l c, levelToks l' n := by
  induction c generalizing l with
  | zero => exact .rfl
  | succ c ih =>
    simp only [levelsToks, List.range'_succ]
    exact (sep_congr .rfl (ih (l + 1))).trans
      (BigSepL.bigSepL_cons (Φ := fun _ l' => levelToks l' n)).symm

/-- Peeling off level `l < T`. -/
theorem threadToksFrom_succ (l n : Nat) (h : l < hT.threadBound) :
    threadToksFrom (GF := GF) l n ⊣⊢ levelToks l n ∗ threadToksFrom (l + 1) n := by
  unfold threadToksFrom
  rw [show hT.threadBound - l = (hT.threadBound - (l + 1)) + 1 by omega]
  exact .rfl

/-- One thread token's levels from `l < T`: level `l` and the levels from `l + 1`. -/
theorem threadTokFrom_succ (l : Nat) (h : l < hT.threadBound) :
    threadTokFrom (GF := GF) l ⊣⊢ levelTok l ∗ threadTokFrom (l + 1) :=
  threadToksFrom_succ l 1 h

/-- No levels from `T` on. -/
theorem threadToksFrom_of_le (l n : Nat) (h : hT.threadBound ≤ l) :
    threadToksFrom (GF := GF) l n ⊣⊢ emp := by
  unfold threadToksFrom
  rw [show hT.threadBound - l = 0 by omega]
  exact .rfl

theorem threadToksFrom_add (l m n : Nat) :
    threadToksFrom (GF := GF) l (m + n) ⊣⊢ threadToksFrom l m ∗ threadToksFrom l n :=
  levelsToks_add _ _ m n

theorem threadToksFrom_zero (l : Nat) : ⊢ threadToksFrom (GF := GF) l 0 :=
  levelsToks_zero _ _

theorem threadToksFrom_bigSepL (l n : Nat) :
    threadToksFrom (GF := GF) l n ⊣⊢
      [∗list] l' ∈ List.range' l (hT.threadBound - l), levelToks l' n :=
  levelsToks_bigSepL _ _ n

/-- `threadToks n` is `n` tokens of each of the levels `0, ..., T - 1`. -/
theorem threadToks_eq_levels (n : Nat) :
    threadToks (GF := GF) n = levelsToks 0 hT.threadBound n := by
  simp [threadToks, threadToksFrom]

/-- `threadToks n` is `threadToksFrom 0 n` (by definition). -/
theorem threadToks_eq_from (n : Nat) : threadToks (GF := GF) n = threadToksFrom 0 n := rfl

/-- `n` thread tokens are `n` tokens of each of the `T` levels. -/
theorem threadToks_bigSepL (n : Nat) :
    threadToks (GF := GF) n ⊣⊢ [∗list] l ∈ List.range hT.threadBound, levelToks l n := by
  rw [List.range_eq_range']
  exact threadToksFrom_bigSepL 0 n

/-- One thread token is one token of each of the `T` levels. -/
theorem threadTok_bigSepL :
    threadTok (GF := GF) ⊣⊢ [∗list] l ∈ List.range hT.threadBound, levelTok l :=
  threadToks_bigSepL 1

/-- A thread token: its level-`0` token and the levels from `1`. -/
theorem threadTok_level0 :
    threadTok (GF := GF) ⊣⊢ levelTok 0 ∗ threadTokFrom 1 :=
  threadTokFrom_succ 0 (by have := hT.threadBound_gt; omega)

/-! ### Whole thread tokens -/

/-- `threadToks (m + n) ⊣⊢ threadToks m ∗ threadToks n`. -/
theorem threadToks_add (m n : Nat) :
    threadToks (GF := GF) (m + n) ⊣⊢ threadToks m ∗ threadToks n :=
  threadToksFrom_add 0 m n

/-- `True ⊢ threadToks 0`. -/
theorem threadToks_zero : ⊢ threadToks (GF := GF) 0 :=
  threadToksFrom_zero 0

/-- `n` tokens: `n < T` (from their level-`0` tokens). -/
theorem threadToks_lt (n : Nat) : threadToks (GF := GF) n ⊢ ⌜n < hT.threadBound⌝ := by
  refine (threadToksFrom_succ 0 n (by have := hT.threadBound_gt; omega)).1.trans ?_
  iintro ⟨H0, -⟩
  iapply levelToks_lt 0 n $$ H0

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
variable {GF : BundledGFunctors} [AllG GF]
open ProofMode

/-- The slots `0, ..., n - 1` of level `l` allocated in the ghost map `γ`, as `n` level-`l`
tokens, the keys from `l * T + n` on staying free. -/
private theorem level_init_aux (T : Nat) (hT : 1 < T) (γ : GName) (l : Nat) (m : GMap Nat Unit)
    (Hfree : ∀ k, l * T ≤ k → m.lookup k = none) (n : Nat) (hn : n ≤ T - 1) :
    ghostMapAuth γ 1 m ⊢@{IProp GF}
      |==> ∃ m' : GMap Nat Unit,
        ghostMapAuth γ 1 m' ∗
        ⌜∀ k, l * T + n ≤ k → m'.lookup k = none⌝ ∗
        levelToks (hT := ⟨γ, T, hT⟩) l n := by
  induction n with
  | zero =>
    iintro Hm
    imodintro
    iexists m
    iframe Hm
    isplitr
    · ipureintro; intro k hk; exact Hfree k (by omega)
    · exact levelToks_zero (hT := ⟨γ, T, hT⟩) l
  | succ n ih =>
    iintro Hm
    imod ih (by omega) $$ Hm with ⟨%m', Hm, %Hfree', Htoks⟩
    imod ghost_map_insert (l * T + n) () (Hfree' _ (Nat.le_refl _)) $$ Hm with ⟨Hm, Htok⟩
    imodintro
    iexists (<[l * T + n := ()]> m')
    iframe Hm
    isplitr
    · ipureintro
      intro k hk
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      exact Hfree' k (by omega)
    · iapply (levelToks_add (hT := ⟨γ, T, hT⟩) l n 1).2
      iframe Htoks
      unfold levelToks
      iexists [n]
      isplitr
      · ipureintro; rfl
      · unfold levelTokList levelTokList
        isplitr
        · ipureintro; show n + 1 < T; omega
        isplitl [Htok]
        · unfold levelKey; iexact Htok
        · iempintro

/-- The levels `l, ..., l + c - 1` allocated, `T - 1` tokens each, the keys from
`(l + c) * T` on staying free. -/
private theorem levels_init_aux (T : Nat) (hT : 1 < T) (γ : GName) (c : Nat) :
    ∀ (l : Nat) (m : GMap Nat Unit), (∀ k, l * T ≤ k → m.lookup k = none) →
    ghostMapAuth γ 1 m ⊢@{IProp GF}
      |==> ∃ m' : GMap Nat Unit,
        ghostMapAuth γ 1 m' ∗
        ⌜∀ k, (l + c) * T ≤ k → m'.lookup k = none⌝ ∗
        levelsToks (hT := ⟨γ, T, hT⟩) l c (T - 1) := by
  induction c with
  | zero =>
    intro l m Hfree
    iintro Hm
    imodintro
    iexists m
    iframe Hm
    isplitr
    · ipureintro; intro k hk; exact Hfree k (by omega)
    · exact levelsToks_zero (hT := ⟨γ, T, hT⟩) l 0
  | succ c ih =>
    intro l m Hfree
    iintro Hm
    imod level_init_aux T hT γ l m Hfree (T - 1) (Nat.le_refl _) $$ Hm with
      ⟨%m', Hm, %Hfree', Hl⟩
    imod ih (l + 1) m' (fun k hk => Hfree' k (by rw [Nat.add_mul] at hk; omega)) $$ Hm with
      ⟨%m'', Hm, %Hfree'', Hls⟩
    imodintro
    iexists m''
    iframe Hm
    isplitr
    · ipureintro
      intro k hk
      exact Hfree'' k (by rw [show l + 1 + c = l + (c + 1) by omega]; exact hk)
    · simp only [levelsToks]
      iframe

/-- Allocation of the thread ghost state for a bound `T > 1`: all `T - 1` tokens, that is
`T - 1` tokens of each of the `T` levels. The adequacy theorem hands one to the main thread and
makes the others the initial thread fuel of the bounded semantics. -/
theorem thread_init (T : Nat) (hT : 1 < T) :
    ⊢@{IProp GF} |==> ∃ γ : GName, threadToks (hT := ⟨γ, T, hT⟩) (T - 1) := by
  simp only [threadToks_eq_levels]
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Unit) with ⟨%γ, Hm⟩
  imod levels_init_aux T hT γ T 0 ∅ (fun _ _ => rfl) $$ Hm with ⟨%m, -, -, Htoks⟩
  imodintro
  iexists γ
  iexact Htoks

end init

end Perennial
