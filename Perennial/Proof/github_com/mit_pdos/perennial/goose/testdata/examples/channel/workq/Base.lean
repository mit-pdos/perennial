/-
A work queue with work stealing (bag and broadcast channel idioms).

Notes:
* Sums over indexed maps are `List.sum (List.mapIdx f l)`; the needed facts are
  proved via two general lemmas `mapIdx_sum_congr`/`mapIdx_sum_update`.
* `Pos.Countable loc` (needed for channels of channels / pointers) comes from
  `Perennial/Proof/time.lean` (`loc_countable`), hence the import.
* The coordinator invariant is a separate definition `coordinatorInv`.

This file: pure helper lemmas, the package's `isPkgInit` instances, the ghost
state of the tasks and the predicates of the coordinator and of the workers.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.time.Base
public import Perennial.Golang.Theory.Chan
public import Perennial.Golang.Theory.Chan.Idioms.Bag
public import Perennial.Golang.Theory.Chan.Idioms.Broadcast
public import Perennial.Ghost.GhostMap
public import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

/-! ### Pure helper lemmas -/

-- (declared before the proofs: a command such as `structure`, `macro` or `notation`
-- declared after asynchronously elaborated proofs waits for them)
local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

structure WorkqNames where
  docs : List GoString
  taskGn : GName

theorem mapSeq_size {A : Type} (start : Nat) (xs : List A) :
    GMap.size (GMap.mapSeq start xs : GMap Nat A) = xs.length := by
  induction xs generalizing start with
  | nil => exact GMap.map_size_empty
  | cons x xs ih =>
    rw [GMap.mapSeq_cons, GMap.map_size_insert_None _ _ _ (GMap.mapSeq_cons_disjoint start xs), ih]
    rfl

theorem mapIdx_sum_congr {A : Type} (h1 h2 : Nat → A → Nat) (l : List A)
    (H : ∀ i d, l[i]? = some d → h1 i d = h2 i d) :
    (l.mapIdx h1).sum = (l.mapIdx h2).sum := by
  induction l generalizing h1 h2 with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapIdx_cons, List.sum_cons]
    rw [H 0 a rfl, ih (fun i => h1 (i + 1)) (fun i => h2 (i + 1)) (fun i d hd => H (i + 1) d hd)]

theorem mapIdx_sum_update {A : Type} (h1 h2 : Nat → A → Nat) (l : List A) (i : Nat) (d : A)
    (Hd : l[i]? = some d) (H : ∀ j x, j ≠ i → l[j]? = some x → h1 j x = h2 j x) :
    (l.mapIdx h1).sum + h2 i d = (l.mapIdx h2).sum + h1 i d := by
  induction l generalizing h1 h2 i with
  | nil => simp at Hd
  | cons a l ih =>
    simp only [List.mapIdx_cons, List.sum_cons]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at Hd
      subst Hd
      rw [mapIdx_sum_congr (fun i => h1 (i + 1)) (fun i => h2 (i + 1)) l
        (fun j x hx => H (j + 1) x (by omega) hx)]
      omega
    | succ i =>
      simp only [List.getElem?_cons_succ] at Hd
      have := ih (fun i => h1 (i + 1)) (fun i => h2 (i + 1)) i Hd
        (fun j x hj hx => H (j + 1) x (by omega) hx)
      rw [H 0 a (by omega) rfl]
      omega

/-- The contribution of document `i`. -/
def countedFn (f : GoString → Nat) (remaining_docs : GMap Nat (Option GoString))
    (i : Nat) (doc : GoString) : Nat :=
  match remaining_docs !! i with
  | some (some _) => 0
  | _ => f doc

/-- The total contribution of the documents not yet counted. -/
abbrev countedSum (f : GoString → Nat) (docs : List GoString)
    (remaining_docs : GMap Nat (Option GoString)) : Nat :=
  (docs.mapIdx (countedFn f remaining_docs)).sum

/-- When all entries in `remaining_docs` are `Some (Some _)`, the imap sum is 0. -/
theorem imap_sum_all_some (f : GoString → Nat) (docs : List GoString)
    (remaining_docs : GMap Nat (Option GoString))
    (Hlookup : ∀ i, i < docs.length → ∃ d, remaining_docs !! i = some (some d)) :
    countedSum f docs remaining_docs = 0 := by
  unfold countedSum
  rw [mapIdx_sum_congr _ (fun _ _ => 0) docs]
  · clear Hlookup; induction docs <;> simp_all [List.mapIdx_cons]
  · intro i d hd
    obtain ⟨d', hd'⟩ := Hlookup i (List.getElem?_eq_some_iff.1 hd).1
    simp only [countedFn, hd']

theorem imap_sum_no_some_some (f : GoString → Nat) (docs : List GoString)
    (remaining_docs : GMap Nat (Option GoString))
    (Hno_some : ∀ i, i < docs.length → ∀ d, remaining_docs !! i ≠ some (some d)) :
    countedSum f docs remaining_docs = (docs.map f).sum := by
  unfold countedSum
  rw [mapIdx_sum_congr _ (fun _ d => f d) docs]
  · clear Hno_some
    induction docs with
    | nil => rfl
    | cons a l ih => simp only [List.mapIdx_cons, List.sum_cons, List.map_cons, ← ih]
  · intro i d hd
    have Hi := (List.getElem?_eq_some_iff.1 hd).1
    unfold countedFn
    split
    · rename_i d' h; exact absurd h (Hno_some i Hi d')
    · rfl

/-- Inserting `None` at position `i` changes only that position's contribution. -/
theorem imap_sum_insert_none (f : GoString → Nat) (docs : List GoString)
    (remaining_docs : GMap Nat (Option GoString)) (i : Nat) (doc : GoString)
    (Hlookup : remaining_docs !! i = some (some doc)) (Hdoc : docs[i]? = some doc) :
    countedSum f docs (<[i := none]> remaining_docs) =
      countedSum f docs remaining_docs + f doc := by
  unfold countedSum
  have := mapIdx_sum_update (countedFn f (<[i := none]> remaining_docs))
    (countedFn f remaining_docs) docs i doc Hdoc
    (fun j x hj _ => by simp only [countedFn, GMap.lookup_insert_eq_iff, Ne.symm hj, ↓reduceIte])
  simp only [countedFn, Hlookup, GMap.lookup_insert_eq_iff, ↓reduceIte] at this
  omega

/-- Deleting a `None` entry doesn't change the imap sum. -/
theorem imap_sum_delete_none (f : GoString → Nat) (docs : List GoString)
    (remaining_docs : GMap Nat (Option GoString)) (i : Nat)
    (Hlookup : remaining_docs !! i = some none) :
    countedSum f docs (remaining_docs.delete i) = countedSum f docs remaining_docs := by
  unfold countedSum
  apply mapIdx_sum_congr
  intro j d _
  by_cases hij : i = j
  · subst hij; simp only [countedFn, GMap.lookup_delete_iff, ↓reduceIte, Hlookup]
  · simp only [countedFn, GMap.lookup_delete_iff, hij, ↓reduceIte]

theorem map_size1_lookup_ne {K V : Type} [DecidableEq K] (m : GMap K V) (i : K) (v : V)
    (h : m !! i = some v) (hs : m.size = 1) (j : K) (hj : j ≠ i) : m !! j = none := by
  have : (GMap.delete i m).size = 0 := by rw [GMap.map_size_delete_Some m i v h, hs]
  have h2 := congrArg (· !! j) (GMap.map_size_empty_inv _ this)
  simpa [GMap.lookup_delete_iff, Ne.symm hj] using h2

theorem sint_nat_sub1 (r : w64) (h : sint.nat r ≠ 0) : sint.nat (r + W64 (-1)) = sint.nat r - 1 := by
  word

theorem mods_2_bound (i : w64) (h0 : 0 ≤ sint.Z i) (h2 : sint.Z i < 2) :
    0 ≤ sint.Z ((i + W64 1).srem (W64 2)) ∧ sint.Z ((i + W64 1).srem (W64 2)) < 2 := by
  have : i = W64 0 ∨ i = W64 1 := by
    by_cases h : i = W64 0
    · exact .inl h
    · right; apply BitVec.eq_of_toInt_eq
      have : sint.Z i ≠ 0 := fun h' => h (BitVec.eq_of_toInt_eq h')
      show sint.Z i = sint.Z (W64 1); rw [show sint.Z (W64 1) = 1 from rfl]; omega
  rcases this with rfl | rfl <;> decide

/-! ### Specifications -/

section init
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics] [package_sem : workq.Assumptions]


instance isPkgInit_inst : IsPkgInit (IProp GF) pkg := define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg := build_get_is_pkg_init_wf

end init

section wps
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq.Assumptions]

def ownTask (γ : WorkqNames) (doc : GoString) : IProp GF :=
  iprop(∃ i : Nat, i ↪[γ.taskGn] (some doc))

/-- A task being `None` means that `total` has it, but remaining hasn't been
decremented yet. -/
def ownTaskAuth (γ : WorkqNames) (remaining_docs : GMap Nat (Option GoString)) : IProp GF :=
  ghostMapAuth γ.taskGn 1 remaining_docs

def word_count (doc : GoString) : Nat := (strings.splitFields doc).length

def isTasksDone (γ : WorkqNames) (sh : shared) : IProp GF :=
  sync.atomic.ownInt64 sh.total' DFrac.discard (W64 ((γ.docs.map word_count).sum : Int))

def coordinatorInv (γ : WorkqNames) (sh : shared) (γdone : ChanNames) : IProp GF :=
  iprop(∃ (remaining_docs : GMap Nat (Option GoString)) (remainingv : w64),
    "H" ∷ (if remainingv = W64 0 then iprop(True)
           else iprop(∃ totalv : w64,
             "Htotal" ∷ sync.atomic.ownInt64 sh.total' (DFrac.own 1) totalv ∗
             "Hdone" ∷ ownBroadcastChan sh.done' γdone (isTasksDone γ sh) .Pending ∗
             "%Htotal" ∷ ⌜totalv = W64 (countedSum word_count γ.docs remaining_docs : Int)⌝)) ∗
    "Hremaining" ∷ sync.atomic.ownInt64 sh.remaining' (DFrac.own 1) remainingv ∗
    "Hauth" ∷ ownTaskAuth γ remaining_docs ∗
    "%Hremaining_size" ∷ ⌜sint.nat remainingv = GMap.size remaining_docs⌝ ∗
    "%Hdocs_agree" ∷ ⌜∀ (i : Nat) (v : Option GoString), remaining_docs !! i = some v →
        match v with | some doc => γ.docs[i]? = some doc | none => True⌝)

def isCoordinator (γ : WorkqNames) (sh : shared) : IProp GF :=
  iprop(∃ γdone : ChanNames,
    "#Hdone" ∷ ownBroadcastChan sh.done' γdone (isTasksDone γ sh) .Unknown ∗
    "#Hdone_is" ∷ isChan sh.done' γdone Unit ∗
    "#Hi" ∷ inv nroot (coordinatorInv γ sh γdone))

instance isCoordinator_persistent (γ : WorkqNames) (sh : shared) :
    Persistent (isCoordinator (GF := GF) γ sh) := by
  unfold isCoordinator; infer_instance

def stealReplyPred (γ : WorkqNames) (maybe_req : Loc) : IProp GF :=
  if maybe_req = null then iprop(True)
  else iprop(∃ req : GoString, maybe_req ↦ req ∗ ownTask γ req)

def isWorker (γ : WorkqNames) (w : Loc) : IProp GF :=
  iprop(∃ (wv : Worker) (γsteal γqueue : ChanNames),
    "#w" ∷ w ↦□ wv ∗
    "#Hqueue" ∷ isChanBag γqueue wv.queue' (ownTask (GF := GF) γ) ∗
    "#Hsteal" ∷ isChanBag γsteal wv.steal'
      (fun (reply : GoChan) => iprop(∃ γreply : ChanNames,
        isChanBag γreply reply (stealReplyPred (GF := GF) γ))))

instance isWorker_persistent (γ : WorkqNames) (w : Loc) :
    Persistent (isWorker (GF := GF) γ w) := by
  unfold isWorker; infer_instance

instance isTasksDone_persistent (γ : WorkqNames) (sh : shared) :
    Persistent (isTasksDone (GF := GF) γ sh) := by
  unfold isTasksDone
  exact as_dfractional_persistent (Φ := fun dq => sync.atomic.ownInt64 (GF := GF) sh.total' dq
    (W64 ((γ.docs.map word_count).sum : Int)))

theorem tasks_to_list (γ : WorkqNames) (start : Nat) (l : List GoString) :
    ([∗map] k ↦ v ∈ GMap.mapSeq start (l.map some), k ↪[γ.taskGn] v) ⊢
      [∗list] d ∈ l, ownTask (GF := GF) γ d := by
  induction l generalizing start with
  | nil =>
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons d l ih =>
    rw [List.map_cons, GMap.mapSeq_cons]
    iintro H
    icases (BigSepM.bigSepM_insert (GMap.mapSeq_cons_disjoint start _)).1 $$ H with ⟨Hd, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hd]
    · unfold ownTask; iexists start; iexact Hd
    · iapply ih $$ H

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

end Perennial
