/-
Port of `new/proof/github_com/mit_pdos/perennial/goose/testdata/examples/channel/workq.v`:
a work queue with work stealing (bag and broadcast channel idioms).

Lean notes:
* stdpp `imap f l` is `List.mapIdx f l` and `sum_list` is `List.sum`; the imap-sum
  lemmas are proved via two general lemmas `mapIdx_sum_congr`/`mapIdx_sum_update`.
* `Pos.Countable loc` (needed for channels of channels / pointers) comes from
  `Perennial/Proof/time.lean` (`loc_countable`), hence the import.
* The coordinator invariant is a separate definition `coordinator_inv` (Rocq inlines it).
-/
import Perennial.Proof.ProofPrelude
import Perennial.Proof.sync.atomic
import Perennial.Proof.strings
import Perennial.Proof.time
import Perennial.Golang.Theory.Chan
import Perennial.Golang.Theory.Chan.Idioms.Bag
import Perennial.Golang.Theory.Chan.Idioms.Broadcast
import Perennial.Ghost.GhostMap
import Perennial.GeneratedProof.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE

namespace github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

/-! ### Pure helper lemmas -/

theorem map_seq_size {A : Type} (start : Nat) (xs : List A) :
    gmap.size (gmap.map_seq start xs : gmap Nat A) = xs.length := by
  induction xs generalizing start with
  | nil => exact gmap.map_size_empty
  | cons x xs ih =>
    rw [gmap.map_seq_cons, gmap.map_size_insert_None _ _ _ (gmap.map_seq_cons_disjoint start xs), ih]
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

/-- The total contribution of the documents not yet counted (Rocq inlines this `imap`). -/
abbrev counted_sum (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string)) : Nat :=
  (docs.mapIdx (fun i doc => match remaining_docs !! i with
    | some (some _) => 0
    | _ => f doc)).sum

/-- When all entries in `remaining_docs` are `Some (Some _)`, the imap sum is 0. -/
theorem imap_sum_all_some (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string))
    (Hlookup : ∀ i, i < docs.length → ∃ d, remaining_docs !! i = some (some d)) :
    counted_sum f docs remaining_docs = 0 := by
  unfold counted_sum
  rw [mapIdx_sum_congr _ (fun _ _ => 0) docs]
  · clear Hlookup; induction docs <;> simp_all [List.mapIdx_cons]
  · intro i d hd
    obtain ⟨d', hd'⟩ := Hlookup i (List.getElem?_eq_some_iff.1 hd).1
    simp only [hd']

theorem imap_sum_no_some_some (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string))
    (Hno_some : ∀ i, i < docs.length → ∀ d, remaining_docs !! i ≠ some (some d)) :
    counted_sum f docs remaining_docs = (docs.map f).sum := by
  unfold counted_sum
  rw [mapIdx_sum_congr _ (fun _ d => f d) docs]
  · clear Hno_some
    induction docs with
    | nil => rfl
    | cons a l ih => simp only [List.mapIdx_cons, List.sum_cons, List.map_cons, ← ih]
  · intro i d hd
    have Hi := (List.getElem?_eq_some_iff.1 hd).1
    split
    · rename_i d' h; exact absurd h (Hno_some i Hi d')
    · rfl

/-- Inserting `None` at position `i` changes only that position's contribution. -/
theorem imap_sum_insert_none (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string)) (i : Nat) (doc : go_string)
    (Hlookup : remaining_docs !! i = some (some doc)) (Hdoc : docs[i]? = some doc) :
    counted_sum f docs (<[i := none]> remaining_docs) =
      counted_sum f docs remaining_docs + f doc := by
  unfold counted_sum
  have := mapIdx_sum_update
    (fun j d => match (<[i := none]> remaining_docs) !! j with | some (some _) => 0 | _ => f d)
    (fun j d => match remaining_docs !! j with | some (some _) => 0 | _ => f d) docs i doc Hdoc
    (fun j x hj _ => by simp only [gmap.lookup_insert_eq_iff, if_neg (Ne.symm hj)])
  simp only [Hlookup, gmap.lookup_insert_eq_iff, if_pos rfl] at this
  omega

/-- Deleting a `None` entry doesn't change the imap sum. -/
theorem imap_sum_delete_none (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string)) (i : Nat)
    (Hlookup : remaining_docs !! i = some none) :
    counted_sum f docs (remaining_docs.delete i) = counted_sum f docs remaining_docs := by
  unfold counted_sum
  apply mapIdx_sum_congr
  intro j d _
  by_cases hij : i = j
  · subst hij; simp only [gmap.lookup_delete_iff, if_pos rfl, Hlookup]
  · simp only [gmap.lookup_delete_iff, if_neg hij]

theorem mods_2_bound (i : w64) (h0 : 0 ≤ sint.Z i) (h2 : sint.Z i < 2) :
    0 ≤ sint.Z ((i + W64 1).smod (W64 2)) ∧ sint.Z ((i + W64 1).smod (W64 2)) < 2 := by
  sorry -- TODO(port)

/-! ### Specifications -/

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics] [package_sem : workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg := define_is_pkg_init iprop(True)
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg := build_get_is_pkg_init_wf

theorem wp_initialize' (get_is_pkg_init : go_string → IProp GF)
    (Hinit : get_is_pkg_init_prop pkg get_is_pkg_init) :
    {{ own_initializing get_is_pkg_init }}
      (App (Val initialize') (Val #()))
    {{ RET #(); own_initializing get_is_pkg_init ∗ is_pkg_init (PROP := IProp GF) pkg }} := by
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  wp_auto
  wp_apply sync.atomic.wp_initialize' _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hatomic⟩
  wp_apply strings.wp_initialize' _ Hinit.2.1 $$ Hown as ⟨Hown, #Hstrings⟩
  iframe Hown
  is_pkg_init_finish

end init

structure workq_names where
  docs : List go_string
  task_gn : GName

section wps
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics] [package_sem : workq.Assumptions]

local notation "pkg" => pkg_id.github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

def own_task (γ : workq_names) (doc : go_string) : IProp GF :=
  iprop(∃ i : Nat, i ↪[γ.task_gn] (some doc))

/-- A task being `None` means that `total` has it, but remaining hasn't been
decremented yet. -/
def own_task_auth (γ : workq_names) (remaining_docs : gmap Nat (Option go_string)) : IProp GF :=
  ghost_map_auth γ.task_gn 1 remaining_docs

def word_count (doc : go_string) : Nat := (split_fields doc).length

def is_tasks_done (γ : workq_names) (sh : shared.t) : IProp GF :=
  sync.atomic.own_Int64 sh.total' DFrac.discard (W64 ((γ.docs.map word_count).sum : Int))

def coordinator_inv (γ : workq_names) (sh : shared.t) (γdone : chan_names) : IProp GF :=
  iprop(∃ (remaining_docs : gmap Nat (Option go_string)) (remainingv : w64),
    "H" ∷ (if remainingv = W64 0 then iprop(True)
           else iprop(∃ totalv : w64,
             "Htotal" ∷ sync.atomic.own_Int64 sh.total' (DFrac.own 1) totalv ∗
             "Hdone" ∷ own_broadcast_chan sh.done' γdone (is_tasks_done γ sh) .Pending ∗
             "%Htotal" ∷ ⌜totalv = W64 (counted_sum word_count γ.docs remaining_docs : Int)⌝)) ∗
    "Hremaining" ∷ sync.atomic.own_Int64 sh.remaining' (DFrac.own 1) remainingv ∗
    "Hauth" ∷ own_task_auth γ remaining_docs ∗
    "%Hremaining_size" ∷ ⌜sint.nat remainingv = gmap.size remaining_docs⌝ ∗
    "%Hdocs_agree" ∷ ⌜∀ (i : Nat) (v : Option go_string), remaining_docs !! i = some v →
        match v with | some doc => γ.docs[i]? = some doc | none => True⌝)

def is_coordinator (γ : workq_names) (sh : shared.t) : IProp GF :=
  iprop(∃ γdone : chan_names,
    "#Hdone" ∷ own_broadcast_chan sh.done' γdone (is_tasks_done γ sh) .Unknown ∗
    "#Hdone_is" ∷ is_chan sh.done' γdone Unit ∗
    "#Hi" ∷ inv nroot (coordinator_inv γ sh γdone))

instance is_coordinator_persistent (γ : workq_names) (sh : shared.t) :
    Persistent (is_coordinator (GF := GF) γ sh) := by
  unfold is_coordinator; infer_instance

def steal_reply_pred (γ : workq_names) (maybe_req : loc) : IProp GF :=
  if maybe_req = null then iprop(True)
  else iprop(∃ req : go_string, maybe_req ↦ req ∗ own_task γ req)

def is_Worker (γ : workq_names) (w : loc) : IProp GF :=
  iprop(∃ (wv : Worker.t) (γsteal γqueue : chan_names),
    "#w" ∷ w ↦□ wv ∗
    "#Hqueue" ∷ is_chan_bag γqueue wv.queue' (own_task (GF := GF) γ) ∗
    "#Hsteal" ∷ is_chan_bag γsteal wv.steal'
      (fun (reply : chan.t) => iprop(∃ γreply : chan_names,
        is_chan_bag γreply reply (steal_reply_pred (GF := GF) γ))))

instance is_Worker_persistent (γ : workq_names) (w : loc) :
    Persistent (is_Worker (GF := GF) γ w) := by
  unfold is_Worker; infer_instance

instance is_tasks_done_persistent (γ : workq_names) (sh : shared.t) :
    Persistent (is_tasks_done (GF := GF) γ sh) := by
  unfold is_tasks_done; exact as_dfractional_persistent

set_option goose.wp.extras true

theorem wp_Worker__process (γ : workq_names) (w : loc) (doc : go_string) (sh : shared.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hcoord" ∷ is_coordinator γ sh ∗
        "Hdoc" ∷ own_task γ doc }}
      (App (App (Val (w @!! go.type.PointerType Worker @!! go!"process")) (Val #doc)) (Val #sh))
    {{ RET #(); True }} := by
  sorry -- TODO(port)

theorem wp_Worker__run (γ : workq_names) (w neighbor : loc) (sh : shared.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hneighbor" ∷ is_Worker γ neighbor ∗
        "#Hcoord" ∷ is_coordinator γ sh }}
      (App (App (Val (w @!! go.type.PointerType Worker @!! go!"run")) (Val #neighbor)) (Val #sh))
    {{ RET #(); True }} := by
  sorry -- TODO(port)

theorem wp_wordCount (docs_sl : slice.t) (docs : List go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ "Hdocs" ∷ docs_sl ↦* docs }}
      (App (Val (@! wordCount)) (Val #docs_sl))
    {{ RET #(W64 ((docs.map word_count).sum : Int)); True }} := by
  sorry -- TODO(port)

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

end Perennial
