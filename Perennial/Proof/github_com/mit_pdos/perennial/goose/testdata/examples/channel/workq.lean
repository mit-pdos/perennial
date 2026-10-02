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

/-- The contribution of document `i` (Rocq inlines this function in an `imap`). -/
def counted_fn (f : go_string → Nat) (remaining_docs : gmap Nat (Option go_string))
    (i : Nat) (doc : go_string) : Nat :=
  match remaining_docs !! i with
  | some (some _) => 0
  | _ => f doc

/-- The total contribution of the documents not yet counted. -/
abbrev counted_sum (f : go_string → Nat) (docs : List go_string)
    (remaining_docs : gmap Nat (Option go_string)) : Nat :=
  (docs.mapIdx (counted_fn f remaining_docs)).sum

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
    simp only [counted_fn, hd']

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
    unfold counted_fn
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
  have := mapIdx_sum_update (counted_fn f (<[i := none]> remaining_docs))
    (counted_fn f remaining_docs) docs i doc Hdoc
    (fun j x hj _ => by simp only [counted_fn, gmap.lookup_insert_eq_iff, Ne.symm hj, ↓reduceIte])
  simp only [counted_fn, Hlookup, gmap.lookup_insert_eq_iff, ↓reduceIte] at this
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
  · subst hij; simp only [counted_fn, gmap.lookup_delete_iff, ↓reduceIte, Hlookup]
  · simp only [counted_fn, gmap.lookup_delete_iff, hij, ↓reduceIte]

theorem map_size1_lookup_ne {K V : Type} [DecidableEq K] (m : gmap K V) (i : K) (v : V)
    (h : m !! i = some v) (hs : m.size = 1) (j : K) (hj : j ≠ i) : m !! j = none := by
  have : (gmap.delete i m).size = 0 := by rw [gmap.map_size_delete_Some m i v h, hs]
  have h2 := congrArg (· !! j) (gmap.map_size_empty_inv _ this)
  simpa [gmap.lookup_delete_iff, Ne.symm hj] using h2

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

def word_count (doc : go_string) : Nat := (strings.split_fields doc).length

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
  unfold is_tasks_done
  exact as_dfractional_persistent (Φ := fun dq => sync.atomic.own_Int64 (GF := GF) sh.total' dq
    (W64 ((γ.docs.map word_count).sum : Int)))

set_option goose.wp.extras true

theorem wp_Worker__process (γ : workq_names) (w : loc) (doc : go_string) (sh : shared.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hcoord" ∷ is_coordinator γ sh ∗
        "Hdoc" ∷ own_task γ doc }}
      (App (App (Val (w @!! go.type.PointerType Worker @!! go!"process")) (Val #doc)) (Val #sh))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hw, #Hcoord, Hdoc⟩
  wp_auto
  wp_apply strings.wp_Fields doc as %sl ⟨Hsl, Hcap⟩
  ihave %Hlen := own_slice_len _ _ _ $$ Hsl
  iNamed Hcoord
  iNamed Hcoord
  iNamed Hdoc
  wp_apply_core sync.atomic.wp_Int64__Add $$ [] [-]
  · iPkgInit
  iinv Hi with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold coordinator_inv
  iNamedSuffix Hi "_inv"
  unfold own_task
  icases Hdoc with ⟨%i, Hdoc⟩
  unfold own_task_auth
  icombine Hauth_inv Hdoc gives %Hlookup
  have Hdoc_i : γ.docs[i]? = some doc := Hdocs_agree_inv i _ Hlookup
  by_cases Hz : remainingv = W64 0
  · exfalso
    have : remaining_docs.size = 0 := by rw [← Hremaining_size_inv, Hz]; rfl
    rw [gmap.map_size_empty_inv _ this] at Hlookup; simp at Hlookup
  simp only [Hz, ↓reduceIte]
  iNamedSuffix H_inv "_inv"
  iexists totalv
  iframe Htotal_inv
  iintro Htotal_inv
  imod ghost_map_update none $$ Hauth_inv Hdoc with ⟨Hauth_inv, Hdoc⟩
  imod Hmask with -
  imod Hclose $$ [Hauth_inv Htotal_inv Hdone_inv Hremaining_inv] with -
  · inext
    iexists (<[i := none]> remaining_docs), remainingv
    simp only [Hz, ↓reduceIte]
    isplitl [Htotal_inv Hdone_inv]
    · iexists _
      iframe
      ipureintro
      rw [imap_sum_insert_none word_count _ _ _ _ Hlookup Hdoc_i, Htotal_inv]
      unfold word_count
      rw [Hlen.1]
      word
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [gmap.map_size_insert_Some _ _ _ _ Hlookup]; exact Hremaining_size_inv
    · intro j v hj
      simp only [gmap.lookup_insert_eq_iff] at hj
      split at hj
      · cases hj; trivial
      · exact Hdocs_agree_inv j v hj
  imodintro
  wp_auto
  wp_apply_core sync.atomic.wp_Int64__Add $$ [] [-]
  · iPkgInit
  iinv Hi with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iNamedSuffix Hi "_inv"
  iexists remainingv
  iframe Hremaining_inv
  iintro Hremaining_inv
  icombine Hauth_inv Hdoc gives %Hlookup0
  imod ghost_map_delete $$ Hauth_inv Hdoc with Hauth_inv
  have Hne0 := gmap.map_size_ne_0_lookup_2 remaining_docs Hlookup0
  have Hsize_del := gmap.map_size_delete_Some remaining_docs i _ Hlookup0
  by_cases Hz0 : remainingv = W64 0
  · exfalso; apply Hne0; rw [← Hremaining_size_inv, Hz0]; rfl
  simp only [Hz0, ↓reduceIte]
  iNamedSuffix H_inv "_inv"
  by_cases Hz1 : remainingv + W64 (-1) = W64 0
  · -- about to close done
    have Hr1 : remainingv = W64 1 := by word
    have Hsize1 : remaining_docs.size = 1 := by rw [← Hremaining_size_inv, Hr1]; rfl
    have Htot : counted_sum word_count γ.docs remaining_docs = (γ.docs.map word_count).sum :=
      imap_sum_no_some_some _ _ _ (fun j _ d hd => by
        by_cases hj : j = i
        · subst hj; rw [Hlookup0] at hd; cases hd
        · rw [map_size1_lookup_ne remaining_docs i _ Hlookup0 Hsize1 j hj] at hd; cases hd)
    imod Hmask with -
    imod Hclose $$ [Hauth_inv Hremaining_inv] with -
    · inext
      iexists (remaining_docs.delete i), remainingv + W64 (-1)
      simp only [Hz1, ↓reduceIte]
      iframe
      ipureintro
      refine ⟨?_, ?_⟩
      · rw [Hsize_del, ← Hremaining_size_inv, Hr1]; rfl
      · intro j v hj
        simp only [gmap.lookup_delete_iff] at hj
        split at hj
        · cases hj
        · exact Hdocs_agree_inv j v hj
    imodintro
    wp_auto
    wp_if_destruct
    · ipersist Htotal_inv
      wp_apply wp_broadcast_chan_close sh.done' γdone (is_tasks_done γ sh) $$ [Hdone_inv Htotal_inv]
        as -
      · iframe
        unfold is_tasks_done
        rw [← Htot, ← Htotal_inv]
        iframe #
      iapply HΦ
      itrivial
    · exfalso; simp_all
  · -- not going to close done
    imod Hmask with -
    imod Hclose $$ [Hauth_inv Hremaining_inv Htotal_inv Hdone_inv] with -
    · inext
      iexists (remaining_docs.delete i), remainingv + W64 (-1)
      simp only [Hz1, ↓reduceIte]
      isplitl [Htotal_inv Hdone_inv]
      · iexists _
        iframe
        ipureintro
        rw [imap_sum_delete_none word_count _ _ _ Hlookup0, Htotal_inv]
      iframe
      ipureintro
      refine ⟨?_, ?_⟩
      · rw [Hsize_del, ← Hremaining_size_inv]
        exact sint_nat_sub1 _ (by rw [Hremaining_size_inv]; exact Hne0)
      · intro j v hj
        simp only [gmap.lookup_delete_iff] at hj
        split at hj
        · cases hj
        · exact Hdocs_agree_inv j v hj
    imodintro
    wp_auto
    wp_if_destruct
    · exfalso; simp_all
    · iapply HΦ
      itrivial

theorem wp_Worker__run (γ : workq_names) (w neighbor : loc) (sh : shared.t) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "#Hw" ∷ is_Worker γ w ∗
        "#Hneighbor" ∷ is_Worker γ neighbor ∗
        "#Hcoord" ∷ is_coordinator γ sh }}
      (App (App (Val (w @!! go.type.PointerType Worker @!! go!"run")) (Val #neighbor)) (Val #sh))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hw, #Hneighbor, #Hcoord⟩
  iNamed Hw
  iNamed Hneighbor
  iNamed Hcoord
  ihave #Hcoord2 := Hcoord
  iNamed Hcoord2
  ihave #Hn2 := Hneighbor
  iunfold is_Worker at Hn2
  icases Hn2 with ⟨%nv, %γsteal_n, %γqueue_n, #Hnpt, #Hqueue_n, #Hsteal_n⟩
  wp_auto
  wp_for
  ihave #Hw2 := Hw
  iunfold is_Worker at Hw2
  icases Hw2 with ⟨%wv, %γsteal, %γqueue, #Hwpt, #Hqueue, #Hsteal⟩
  icases Hwpt with ∗Hwpt
  iStructNamed Hwpt
  wp_auto_lc 2
  wp_apply_core chan.wp_select_nonblocking
  isplit
  · iapply BigAndL.bigAndL_cons.2
    isplit
    · -- done
      dsimp only [chan.nonblocking_clause_pre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sh.done', γdone
      isplitr
      · ipureintro; rfl
      iframe #
      iapply blocking_rcv_implies_nonblocking
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
      iintro ⟨#Htasks, -⟩
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- get a request
      dsimp only [chan.nonblocking_clause_pre]
      iexists go_string, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
      isplitr
      · ipureintro; rfl
      ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
      iframe Hqch
      iapply blocking_rcv_implies_nonblocking
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_Worker__process γ w v sh $$ [Hv]
      · iframe #
        iframe
      wp_for_post
      iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- help a worker steal from this one
      dsimp only [chan.nonblocking_clause_pre]
      iexists chan.t, inferInstance, inferInstance, inferInstance, inferInstance, wv.steal', γsteal
      isplitr
      · ipureintro; rfl
      ihave #Hsch := is_bag_is_chan _ _ _ $$ Hsteal
      iframe Hsch
      iapply blocking_rcv_implies_nonblocking
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hsteal
      inext
      iintro %reply_ch ⟨%γreply, #Hreply_ch⟩
      wp_auto_lc 2
      wp_apply_core chan.wp_select_nonblocking
      isplit
      · iapply BigAndL.bigAndL_singleton.2
        dsimp only [chan.nonblocking_clause_pre]
        iexists go_string, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
        isplitr
        · ipureintro; rfl
        ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
        iframe Hqch
        iapply blocking_rcv_implies_nonblocking
        iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
        inext
        iintro %v Hv
        wp_auto
        wp_apply wp_bag_send γreply reply_ch doc_ptr (steal_reply_pred γ) $$ [Hv doc]
        · iframe #
          unfold steal_reply_pred
          split
          · itrivial
          · iexists v
            iframe
        wp_for_post
        iframe
      · wp_auto
        wp_apply wp_bag_send γreply reply_ch null (steal_reply_pred γ) $$ []
        · iframe #
          unfold steal_reply_pred
          simp only [↓reduceIte]
          itrivial
        wp_for_post
        iframe
    · iapply BigAndL.bigAndL_nil.2
      itrivial
  · -- default case; try to steal
    wp_auto
    wp_apply chan.wp_make2 (V := loc) (W64 1) $$ [] as %reply %γreply ⟨#Hreply_is, -, Hown⟩
    · ipureintro; decide
    imod start_bag (steal_reply_pred (GF := GF) γ) _ reply γreply (by simp) $$ Hreply_is Hown with #Hreply
    icases Hnpt with ∗Hnpt
    iStructNamed Hnpt
    wp_auto_lc 2
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- done
      dsimp only [chan.blocking_clause_pre]
      iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sh.done', γdone
      isplitr
      · ipureintro; rfl
      iframe #
      iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone
      iintro ⟨#Htasks, -⟩
      wp_auto
      wp_for_post
      iapply HΦ
      itrivial
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- request to steal was sent
      dsimp only [chan.blocking_clause_pre]
      iexists chan.t, inferInstance, inferInstance, inferInstance, inferInstance, nv.steal', γsteal_n,
        reply
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      ihave #Hnsch := is_bag_is_chan _ _ _ $$ Hsteal_n
      iframe Hnsch
      iapply bag_send_au $$ [$Hlc1 $Hlc2] Hsteal_n []
      · iexists γreply
        iframe #
      inext
      wp_auto
      wp_apply wp_bag_receive γreply reply (steal_reply_pred γ) $$ Hreply as %v Hv
      wp_if_destruct
      · wp_for_post
        iframe
      · unfold steal_reply_pred
        simp only [Hif, ↓reduceIte]
        icases Hv with ⟨%req, Hreq, Htask⟩
        wp_auto
        wp_apply wp_Worker__process γ w req sh $$ [Htask]
        · iframe #
          iframe
        wp_for_post
        iframe
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- received local work while trying to steal
      dsimp only [chan.blocking_clause_pre]
      iexists go_string, inferInstance, inferInstance, inferInstance, inferInstance, wv.queue', γqueue
      isplitr
      · ipureintro; rfl
      ihave #Hqch := is_bag_is_chan _ _ _ $$ Hqueue
      iframe Hqch
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hqueue
      inext
      iintro %v Hv
      wp_auto
      wp_apply wp_Worker__process γ w v sh $$ [Hv]
      · iframe #
        iframe
      wp_for_post
      iframe
    · iapply BigAndL.bigAndL_nil.2
      itrivial

theorem tasks_to_list (γ : workq_names) (start : Nat) (l : List go_string) :
    ([∗map] k ↦ v ∈ gmap.map_seq start (l.map some), k ↪[γ.task_gn] v) ⊢
      [∗list] d ∈ l, own_task (GF := GF) γ d := by
  induction l generalizing start with
  | nil =>
    iintro -
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons d l ih =>
    rw [List.map_cons, gmap.map_seq_cons]
    iintro H
    icases (BigSepM.bigSepM_insert (gmap.map_seq_cons_disjoint start _)).1 $$ H with ⟨Hd, H⟩
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hd]
    · unfold own_task; iexists start; iexact Hd
    · iapply ih $$ H

set_option maxHeartbeats 1000000 in
theorem wp_wordCount (docs_sl : slice.t) (docs : List go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ "Hdocs" ∷ docs_sl ↦* docs }}
      (App (Val (@! wordCount)) (Val #docs_sl))
    {{ RET #(W64 ((docs.map word_count).sum : Int)); True }} := by
  wp_start as Hdocs
  iNamed Hdocs
  wp_auto
  ihave %Hdocs_len := own_slice_len _ _ _ $$ Hdocs
  wp_if_destruct
  · have : docs = [] := List.eq_nil_of_length_eq_zero (by rw [Hdocs_len.1, Hif]; rfl)
    subst this
    rw [show (W64 (((([] : List go_string).map word_count).sum : Nat) : Int)) = W64 0 from rfl]
    iapply HΦ
    itrivial
  wp_apply wp_slice_make2 (V := loc) (W64 2) $$ [] as %workers_sl ⟨workers_sl, -⟩
  · ipureintro; decide
  rename_i j_ptr
  irename : (j_ptr ↦ zero_val w64 : IProp GF) => j
  imod ghost_map_alloc (gmap.map_seq 0 (docs.map some)) with ⟨%γtask_gn, Hauth, Htasks⟩
  ihave HI : (∃ (i j : w64) (workers : List loc),
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ j_ptr ↦ j ∗
      "workers_sl" ∷ workers_sl ↦* (workers ++ List.replicate (2 - sint.nat i) null) ∗
      "#Hworkers" ∷ □ (∀ w, ⌜w ∈ workers⌝ → is_Worker ⟨docs, γtask_gn⟩ w) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 2 ∧ workers.length = sint.nat i⌝ : IProp GF)
    $$ [i j workers_sl]
  · iexists W64 0, _, []
    rw [show ([zero_val loc, zero_val loc] : List loc) =
      [] ++ List.replicate (2 - sint.nat (W64 0)) null from rfl]
    iframe
    isplitr
    · imodintro; iintro %w %Hw; simp at Hw
    · ipureintro; decide
  wp_for HI
  ihave %Hwl := own_slice_len _ _ _ $$ workers_sl
  simp only [List.length_append, List.length_replicate] at Hwl
  by_cases hP : sint.Z i < sint.Z workers_sl.len
  · simp only [hP, decide_true, ↓reduceIte]
    wp_auto
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl (sint.Z i) _ _ null Hi.1 $$ [workers_sl] as workers_sl
    · iframe
      ipureintro
      have h1 := Hi.2.2
      have h2 := Hwl.1
      simp only [sint.nat, sint.Z] at h1 h2 hP ⊢
      rw [List.getElem?_append_right (by omega), List.getElem?_replicate_of_lt (by omega)]
    wp_apply chan.wp_make2 (V := go_string) docs_sl.len $$ [] as %queue %γqueue ⟨#Hq_is, %Hqcap, Hq_own⟩
    · ipureintro; exact Hdocs_len.2
    wp_apply chan.wp_make1 (V := chan.t) as %steal %γsteal ⟨#Hs_is, %Hscap, Hs_own⟩
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    irename «$r0» => Hwr
    imod (typed_pointsto_dfractional (GF := GF) «$r0_ptr»
      ({ queue' := queue, steal' := steal } : Worker.t)).dfractional_persist _ $$ Hwr with #Hwr
    simp only [Hif, ↓reduceIte]
    imod start_bag (own_task (GF := GF) ⟨docs, γtask_gn⟩) _ queue γqueue (by trivial)
      $$ Hq_is Hq_own with #Hqueue
    imod start_bag (fun (reply : chan.t) => iprop(∃ γreply : chan_names,
        is_chan_bag γreply reply (steal_reply_pred (GF := GF) ⟨docs, γtask_gn⟩))) _ steal γsteal
      (by trivial) $$ Hs_is Hs_own with #Hsteal
    wp_apply wp_store_slice_index workers_sl (sint.Z i) _ «$r0_ptr» $$ [workers_sl] as workers_sl
    · iframe
      ipureintro
      simp only [List.length_append, List.length_replicate]
      have h0 := Hi
      have h2 := Hwl.1
      simp only [sint.nat, sint.Z] at h0 h2 hP ⊢
      omega
    wp_for_post
    iframe
    iexists i + W64 1, i, workers ++ [«$r0_ptr»]
    have h0 := Hi
    have h2 := Hwl.1
    simp only [sint.nat, sint.Z] at h0 h2 hP
    have hi1 : (i + W64 1).toInt = i.toInt + 1 := by word
    obtain ⟨k, hk⟩ : ∃ k, 2 - i.toInt.toNat = k + 1 := ⟨2 - i.toInt.toNat - 1, by omega⟩
    rw [show (workers ++ List.replicate (2 - sint.nat i) null).set (sint.Z i).toNat «$r0_ptr» =
        workers ++ [«$r0_ptr»] ++ List.replicate (2 - sint.nat (i + W64 1)) null by
      simp only [sint.nat, sint.Z, hi1, hk, List.replicate_succ]
      rw [show i.toInt.toNat = workers.length by omega, List.set_append_right _ _ (by omega)]
      simp only [Nat.sub_self, List.set_cons_zero, List.append_assoc, List.singleton_append]
      rw [show 2 - (BitVec.toInt i + 1).toNat = k by omega]]
    iframe
    isplitr
    · imodintro
      iintro %w %Hw
      rcases List.mem_append.1 Hw with Hw | Hw
      · iapply Hworkers $$ %w %Hw
      · simp only [List.mem_singleton] at Hw
        subst Hw
        unfold is_Worker
        iexists ({ queue' := queue, steal' := steal } : Worker.t), γsteal, γqueue
        iframe #
    · ipureintro
      simp only [sint.nat, sint.Z, hi1, List.length_append, List.length_singleton]
      omega
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  have h0 := Hi
  have h2 := Hwl.1
  simp only [sint.nat, sint.Z] at h0 h2 hP
  have Hwlen : workers.length = 2 := by omega
  rw [show List.replicate (2 - sint.nat i) null = ([] : List loc) by
    simp only [sint.nat, List.replicate_eq_nil_iff]; omega, List.append_nil]
  wp_auto
  ihave Htasks := tasks_to_list ⟨docs, γtask_gn⟩ 0 docs $$ Htasks
  ihave HI : (∃ (i : w64) (d : go_string),
      "doc" ∷ doc_ptr ↦ d ∗
      "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z docs_sl.len⌝ ∗
      "Htasks" ∷ [∗list] d ∈ docs.drop (sint.nat i), own_task (GF := GF) ⟨docs, γtask_gn⟩ d : IProp GF)
    $$ [doc i Htasks]
  · iexists W64 0, _
    rw [show sint.nat (W64 0) = 0 from rfl, List.drop_zero]
    iframe
    ipureintro; exact ⟨by decide, Hdocs_len.2⟩
  wp_for HI
  by_cases hP : sint.Z i < sint.Z docs_sl.len
  · simp only [hP, _root_.decide_true, ↓reduceIte]
    wp_auto
    simp only [Hi.1, hP, and_self, ↓reduceIte]
    have hlt : sint.nat i < docs.length := by
      have := Hdocs_len.1; simp only [sint.nat, sint.Z] at this hP Hi ⊢; omega
    obtain ⟨dc, Hdc⟩ : ∃ dc, docs[sint.nat i]? = some dc := ⟨_, List.getElem?_eq_getElem hlt⟩
    wp_apply wp_load_slice_index docs_sl (sint.Z i) docs _ dc Hi.1 $$ [Hdocs] as Hdocs
    · iframe; ipureintro; exact Hdc
    ihave %Hwl2 := own_slice_len _ _ _ $$ workers_sl
    rw [Hwlen] at Hwl2
    have hw0 : (0 : Int) < sint.Z workers_sl.len := by
      have := Hwl2.1; simp only [sint.nat, sint.Z] at this ⊢; omega
    obtain ⟨w0, Hw0⟩ : ∃ w0, workers[0]? = some w0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    simp only [show sint.Z (W64 0) = 0 from rfl, Int.le_refl, hw0, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl 0 workers _ w0 (Int.le_refl _) $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hw0
    ihave Hw := Hworkers $$ %w0 %(List.mem_of_getElem? Hw0)
    iunfold is_Worker at Hw
    icases Hw with ⟨%wv, %γsteal, %γqueue, #Hwpt, #Hqueue, #Hsteal⟩
    icases Hwpt with ∗Hwpt
    iStructNamed Hwpt
    wp_auto
    rw [List.drop_eq_getElem_cons hlt]
    icases BigSepL.bigSepL_cons.1 $$ Htasks with ⟨Hdoc, Htasks⟩
    rw [(List.getElem?_eq_some_iff.1 Hdc).2]
    wp_apply wp_bag_send γqueue wv.queue' dc (own_task (GF := GF) ⟨docs, γtask_gn⟩) $$ [Hdoc]
    · iframe #; iframe
    wp_for_post
    iframe
    iexists i + W64 1, dc
    have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by
      simp only [sint.nat, sint.Z] at hP Hi ⊢; word
    rw [hi1]
    iframe
    ipureintro
    simp only [sint.Z] at hP Hi ⊢
    word
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  iclear Htasks
  wp_auto
  ihave Hrem : sync.atomic.own_Int64 (GF := GF) «$v0_ptr» (DFrac.own 1) (W64 0) $$ [«$v0»]
  · rw [sync.atomic.own_Int64_unseal]
    unfold sync.atomic.own_Int64_def
    rw [show ({ _0' := zero_val _, _1' := zero_val _, v' := W64 0 } : sync.atomic.Int64.t) =
      zero_val _ from rfl]
    iexact «$v0»
  ihave Htot : sync.atomic.own_Int64 (GF := GF) «$v1_ptr» (DFrac.own 1) (W64 0) $$ [«$v1»]
  · rw [sync.atomic.own_Int64_unseal]
    unfold sync.atomic.own_Int64_def
    rw [show ({ _0' := zero_val _, _1' := zero_val _, v' := W64 0 } : sync.atomic.Int64.t) =
      zero_val _ from rfl]
    iexact «$v1»
  wp_apply chan.wp_make1 (V := Unit) as %done %γdone ⟨#Hdone_is, %Hdcap, Hdone⟩
  wp_apply_core sync.atomic.wp_Int64__Store $$ [] [-]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Hrem
  iintro Hrem
  imod Hmask with -
  imodintro
  wp_auto
  imod alloc_broadcast_chan (E := ⊤)
    (is_tasks_done (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩) γdone done
    $$ Hdone_is Hdone with Hopen
  ihave #Hdone_unk := own_broadcast_chan_Unknown _ _ _ _ $$ Hopen
  imod inv_alloc nroot ⊤ (coordinator_inv (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩ γdone)
    $$ [Hopen Htot Hrem Hauth] with #Hinv
  · inext
    unfold coordinator_inv own_task_auth
    iexists gmap.map_seq 0 (docs.map some), docs_sl.len
    simp only [Hif, ↓reduceIte]
    isplitl [Htot Hopen]
    · iexists W64 0
      iframe
      ipureintro
      rw [imap_sum_all_some]
      · rfl
      · intro j hj
        exact ⟨docs[j], by simp [gmap.lookup_map_seq_0, List.getElem?_eq_getElem hj]⟩
    iframe
    ipureintro
    refine ⟨?_, ?_⟩
    · rw [map_seq_size, List.length_map, Hdocs_len.1]
    · intro j v hj
      rw [gmap.lookup_map_seq_0, List.getElem?_map] at hj
      cases h : docs[j]? with
      | none => simp [h] at hj
      | some d' =>
        simp only [h, Option.map_some, Option.some.injEq] at hj
        subst hj
        simp
  ihave #Hcoord : is_coordinator (GF := GF) ⟨docs, γtask_gn⟩ ⟨«$v0_ptr», «$v1_ptr», done⟩ $$ []
  · unfold is_coordinator
    iexists γdone
    iframe #
  rename_i jj_ptr
  irename : (jj_ptr ↦ zero_val w64 : IProp GF) => j
  ihave HI : (∃ (i j : w64) (wv : loc),
      "w" ∷ w_ptr ↦ wv ∗
      "i" ∷ i_ptr ↦ i ∗
      "j" ∷ jj_ptr ↦ j ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 2⌝ : IProp GF) $$ [w i j]
  · iexists W64 0, _, _
    iframe
    ipureintro; decide
  ihave %Hwl3 := own_slice_len _ _ _ $$ workers_sl
  rw [Hwlen] at Hwl3
  have hwlen2 : sint.Z workers_sl.len = 2 := by
    have := Hwl3.1; simp only [sint.nat, sint.Z] at this ⊢; omega
  wp_for HI
  by_cases hP : sint.Z i < sint.Z workers_sl.len
  · simp only [hP, _root_.decide_true, ↓reduceIte]
    wp_auto
    rw [hwlen2] at hP
    have hlt : sint.nat i < workers.length := by
      rw [Hwlen]; simp only [sint.nat, sint.Z] at hP Hi ⊢; omega
    obtain ⟨w, Hw⟩ : ∃ w, workers[sint.nat i]? = some w := ⟨_, List.getElem?_eq_getElem hlt⟩
    simp only [Hi.1, hwlen2, hP, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl (sint.Z i) workers _ w Hi.1 $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hw
    have Hb := mods_2_bound i Hi.1 hP
    have hlt2 : sint.nat ((i + W64 1).srem (W64 2)) < workers.length := by
      rw [Hwlen]; simp only [sint.nat, sint.Z] at Hb ⊢; omega
    obtain ⟨nb, Hnb⟩ : ∃ nb, workers[sint.nat ((i + W64 1).srem (W64 2))]? = some nb :=
      ⟨_, List.getElem?_eq_getElem hlt2⟩
    simp only [Hb.1, Hb.2, hwlen2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index workers_sl _ workers _ nb Hb.1 $$ [workers_sl] as workers_sl
    · iframe; ipureintro; exact Hnb
    ihave #Hw := Hworkers $$ %w %(List.mem_of_getElem? Hw)
    ihave #Hnb := Hworkers $$ %nb %(List.mem_of_getElem? Hnb)
    wp_auto
    wp_apply wp_fork $$ []
    · wp_apply wp_Worker__run ⟨docs, γtask_gn⟩ w nb ⟨«$v0_ptr», «$v1_ptr», done⟩ $$ []
      · iframe #
      itrivial
    wp_for_post
    iframe
    iexists i + W64 1, i, w
    iframe
    ipureintro
    simp only [sint.Z] at hP Hi ⊢
    word
  simp only [hP, decide_false, Bool.false_eq_true, ↓reduceIte]
  cleanup_bool_decide
  wp_auto
  wp_apply_core chan.wp_receive (V := Unit) done γdone $$ Hdone_is [-]
  iintro -
  iapply broadcast_chan_receive _ _ _ _ _ $$ Hdone_unk
  iintro ⟨#Htotal, -⟩
  wp_auto
  wp_apply_core sync.atomic.wp_Int64__Load $$ [] [-]
  · iPkgInit
  unfold is_tasks_done
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists _
  iframe Htotal
  iintro -
  imod Hmask with -
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end wps

end github_com.mit_pdos.perennial.goose.testdata.examples.channel.workq

end Perennial
