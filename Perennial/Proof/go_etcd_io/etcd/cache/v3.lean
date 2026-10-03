/-
Port of `new/proof/go_etcd_io/etcd/cache/v3.v`.

Lean notes:
* The proofs live in namespace `go_etcd_io.etcd.cache.v3_proof` (Rocq: top
  level), since Rocq's `kvItem` would clash with the generated Go type
  `go_etcd_io.etcd.cache.v3.kvItem`.
* The axioms bind their package assumptions (`[package_sem : cache.Assumptions]`)
  explicitly.
* The `rpctypes` init instance here carries `is_rpctypes_init` (as in Rocq's
  `cache/v3.v`); Rocq's `leasing.v` declares a `True` one, so (as in Rocq) the
  two files should not be imported together.
* `wp_Cache__Get` (Rocq: `Admitted`, after the `LatestRev` call) is proved, with
  two statement changes:
  - Old (Rocq): precondition `is_pkg_init cache ∗ opts_sl ↦* opts ∗ own_Cache c`.
    New: also `is_OpOptions opts pfx fk` (`client/v3_proof/op.lean`) for some
    `pfx fk` with `¬ (pfx ∧ fk)`. Why: `Get` calls `clientv3.OpGet(key, opts...)`,
    which runs every option closure three times (`IsOptsWithPrefix`,
    `IsOptsWithFromKey`, `applyOpts`), so the closures need a spec; and `OpGet`
    panics if both a `WithPrefix` and a `WithFromKey` option are given.
  - New hypothesis `Hspecs : Cache_Get_callee_specs`: specs of `Cache.WaitReady`,
    `Cache.validateGet`, `Cache.serverRevision`, `Cache.waitTillRevision` and
    `store.Get`. Why: goose does not translate these methods (`cache/v3.toml`
    does not list them), so `cache.v3.Assumptions` has no `MethodUnfold` for them
    and their calls have no semantics; their specs cannot be proved here, and
    they are taken as a hypothesis rather than as axioms. Each spec takes and
    returns `own_Cache c` (resp. `own_store`) and returns arbitrary results;
    `validateGet` also gets `is_Op op (.Get req)`, and `store.Get` the persistent
    slices `startKey ↦*□ _ ∗ endKey ↦*□ _`.
  The postcondition (`True`) is unchanged. `wp_Cache__Get` depends (through
  `own_Cache`'s `c ↦ cv`, i.e. `TypedPointsto cache.v3.Cache.t`) on the
  generated `sorry` instances `Config_typed_pointsto`/`Config_into_val_typed`
  and `progressRequestor_typed_pointsto`/`progressRequestor_into_val_typed` of
  `Perennial/GeneratedProof/go_etcd_io/etcd/cache/v3.lean`.
-/
import Perennial.Code.go_etcd_io.etcd.cache.v3
import Perennial.GeneratedProof.go_etcd_io.etcd.cache.v3
import Perennial.Proof.sync
import Perennial.Proof.sort
import Perennial.Proof.fmt
import Perennial.Proof.go_etcd_io.etcd.client.v3
import Perennial.Proof.k8s_io.utils.third_party.forked.golang.btree

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option autoImplicit false
set_option goose.wp.extras true

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open go_etcd_io.etcd.client.v3_proof k8s_io.utils.third_party.forked.golang.btree

namespace go_etcd_io.etcd.cache.v3_proof

section init
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : heapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : cache.v3.Assumptions]

instance rpc_status_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  define_is_pkg_init iprop(True)
instance rpc_status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.genproto.googleapis.rpc.status :=
  build_get_is_pkg_init_wf

instance status_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.status :=
  define_is_pkg_init iprop(True)
instance status_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.status :=
  build_get_is_pkg_init_wf

instance codes_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  define_is_pkg_init iprop(True)
instance codes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.google_golang_org.grpc.codes :=
  build_get_is_pkg_init_wf

abbrev is_rpctypes_init : IProp GF :=
  iprop(∃ (err_future_rev err_compacted : interface.t_ok),
    "#ErrFutureRev" ∷ (global_addr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrFutureRev) ↦□
      interface.ok err_future_rev ∗
    "#ErrCompacted" ∷ (global_addr go_etcd_io.etcd.api.v3.v3rpc.rpctypes.ErrCompacted) ↦□
      interface.ok err_compacted)
instance rpctypes_is_pkg_init_inst :
    IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  define_is_pkg_init is_rpctypes_init
instance rpctypes_get_is_pkg_init_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes :=
  build_get_is_pkg_init_wf

abbrev is_init : IProp GF :=
  iprop(∃ (err_not_ready : interface.t_ok),
    "#ErrNotRead" ∷ (global_addr cache.v3.ErrNotReady) ↦□ interface.ok err_not_ready)
instance is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  define_is_pkg_init is_init
instance get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 :=
  build_get_is_pkg_init_wf

theorem is_init_access :
    is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ⊢ is_init :=
  is_pkg_init_access (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3

theorem is_rpctypes_init_access :
    is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes ⊢ is_rpctypes_init :=
  is_pkg_init_access (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes

end init

/-! ### Ring buffer -/

/-- If `buf` reaches capacity, the first entry may be removed during Append() to
make space. -/
axiom own_ringBuffer {GF : BundledGFunctors} (r : loc) {T' : Type} [ZeroVal T']
  [TypedPointsto (GF := GF) T'] {V : Type}
  (is_item : T' → V → IProp GF) (rev_item : V → w64) (buf : List V) : IProp GF

axiom wp_ringBuffer__PeekOldest [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : heapGS hlc GF] [sem : go.Semantics] [package_sem : cache.v3.Assumptions]
    {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type} {T : go.type}
    [IntoValTyped (GF := GF) T' T] {is_item : T' → V → IProp GF} {rev_item : V → w64}
    (r : loc) (buf : List V) :
  {{ is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      own_ringBuffer r is_item rev_item buf }}
    (App (Val (r @!! go.type.PointerType (cache.v3.ringBuffer T) @!! go!"PeekOldest")) (Val #()))
  {{ RET #((buf.map rev_item).headD (W64 0)); own_ringBuffer r is_item rev_item buf }}

/-- Rocq's `let iter_itemvs := ...` in `wp_ringBuffer__DescendLessOrEqual`: the
items visited by `DescendLessOrEqual pivot`, in visiting order. -/
def iter_itemvs {V : Type} (rev_item : V → w64) (pivot : w64) (buf : List V) : List V :=
  (buf.filter (fun item => decide (sint.Z (rev_item item) ≤ sint.Z pivot))).reverse

/-- `P i` is the invariant that holds after `iter` has been called `i` times on
the appropriate items. -/
axiom wp_ringBuffer__DescendLessOrEqual [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [go_gctx : GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [hG : heapGS hlc GF] [sem : go.Semantics] [package_sem : cache.v3.Assumptions]
    {T' : Type} [ZeroVal T'] [TypedPointsto (GF := GF) T'] {V : Type} {T : go.type}
    [IntoValTyped (GF := GF) T' T] {is_item : T' → V → IProp GF} {rev_item : V → w64}
    (P : Nat → IProp GF) (pivot : w64) (iter : func.t) (r : loc) (buf : List V)
    (Φ : val → IProp GF) :
  ⊢ (is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
     own_ringBuffer r is_item rev_item buf ∗
     P 0) -∗
    (∀ (i : Nat) (item : T') (itemv : V),
      □ (∀ Ψ : val → IProp GF,
        (P i ∗ ⌜(iter_itemvs rev_item pivot buf)[i]? = some itemv⌝ ∗ is_item item itemv) -∗
        ▷ (∀ («continue» : Bool),
            (if «continue» then P (i + 1) else (own_ringBuffer r is_item rev_item buf -∗ Φ #())) -∗
            Ψ #«continue») -∗
        WP (App (App (Val #iter) (Val #(rev_item itemv))) (Val #item)) {{ Ψ }})) -∗
    (own_ringBuffer r is_item rev_item buf -∗ P (iter_itemvs rev_item pivot buf).length -∗ Φ #()) -∗
    (WP (App (App (Val (r @!! go.type.PointerType (cache.v3.ringBuffer T) @!! go!"DescendLessOrEqual"))
      (Val #pivot)) (Val #iter)) {{ Φ }})

/-! ### Store -/

/-- For BTree. -/
def kvItem : Type := go_string ⊕ KeyValue.t
axiom is_kvItem {GF : BundledGFunctors} : loc → kvItem → IProp GF
axiom less_kvItem : kvItem → kvItem → Prop

/-- For ringbuffer. -/
abbrev snap : Type := w64 × List KeyValue.t

instance own_BTree_discard_persistent [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi]
    [ffi_semantics ext ffi] [GoGlobalContext] {hlc : HasLC} {GF : BundledGFunctors}
    [heapGS hlc GF] [go.Semantics] (t : loc) {T' : Type} [ZeroVal T']
    [TypedPointsto (GF := GF) T'] {V : Type} (is_item : T' → V → IProp GF) (less : V → V → Prop)
    (items : List V) : Persistent (own_BTree t is_item less items DFrac.discard) :=
  (own_BTree_dfractional t is_item less items).dfractional_persistent

axiom is_etcd_kvs {GF : BundledGFunctors} (revision : w64) («prefix» : go_string)
  (key_values : gmap go_string KeyValue.t) : IProp GF
axiom is_etcd_kvmap_pers {GF : BundledGFunctors} (revision : w64) («prefix» : go_string)
  (key_values : gmap go_string KeyValue.t) :
  Persistent (is_etcd_kvs (GF := GF) revision «prefix» key_values)
attribute [instance] is_etcd_kvmap_pers

def ordered_kvs_to_map (kvs : List KeyValue.t) : gmap go_string KeyValue.t :=
  gmap.ofList (kvs.map (fun kv => (kv.key, kv)))

def rev_snapshotItem : snap → w64 := Prod.fst

theorem filter_reverse_head {α : Type} (p : α → Bool) (l : List α) (x : α)
    (h : (l.filter p).reverse[0]? = some x) :
    ∃ i : Nat, l[i]? = some x ∧ p x = true ∧ ∀ (j : Nat) y, i < j → l[j]? = some y → p y = false := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    by_cases hnil : l.filter p = []
    · have hall : ∀ y ∈ l, p y = false := by
        intro y hy
        have := List.filter_eq_nil_iff.mp hnil y hy
        simpa using this
      by_cases ha : p a = true
      · rw [List.filter_cons_of_pos ha, hnil] at h
        simp at h
        subst h
        refine ⟨0, rfl, ha, ?_⟩
        intro j y hj hy
        cases j with
        | zero => omega
        | succ j =>
          simp only [List.getElem?_cons_succ] at hy
          exact hall y (List.mem_of_getElem? hy)
      · rw [List.filter_cons_of_neg ha, hnil] at h
        simp at h
    · have h' : (l.filter p).reverse[0]? = some x := by
        by_cases ha : p a = true
        · rw [List.filter_cons_of_pos ha] at h
          rw [List.reverse_cons, List.getElem?_append_left] at h
          · exact h
          · simp only [List.length_reverse]
            exact List.length_pos_iff.mpr hnil
        · rw [List.filter_cons_of_neg ha] at h
          exact h
      obtain ⟨i, hi, hpx, hlater⟩ := ih h'
      refine ⟨i + 1, by simpa using hi, hpx, ?_⟩
      intro j y hj hy
      cases j with
      | zero => omega
      | succ j =>
        simp only [List.getElem?_cons_succ] at hy
        exact hlater j y (by omega) hy

structure store_names where
  latest_rev_gn : GName

section store
variable [ext : ffi_syntax] [ffi : ffi_model] [ffi_interp ffi] [ffi_semantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : heapGS HasLC.hasLC GF] [allG GF]
variable [sem : go.Semantics]
variable [package_sem : cache.v3.Assumptions]

local notation "pkg" => pkg_id.go_etcd_io.etcd.cache.v3

def is_snapshotItem (l : loc) (s : snap) : IProp GF :=
  iprop(∃ (tree : loc),
    "#snapshot" ∷ l ↦□ (cache.v3.snapshot.t.mk s.1 tree) ∗
    "#tree" ∷ own_BTree tree is_kvItem less_kvItem (s.2.map Sum.inr) DFrac.discard)

instance is_snapshotItem_pers (l : loc) (s : snap) : Persistent (is_snapshotItem (GF := GF) l s) := by
  unfold is_snapshotItem; infer_instance

/-- Cannot be persistent because of RWMutex. -/
def own_store (s : loc) (γstore : store_names) («prefix» : go_string) : IProp GF :=
  iprop(
  "Hmu" ∷ sync.own_RWMutex (s.[cache.v3.store.t, go!"mu"])
    (fun q => iprop(∃ (snapshot : cache.v3.snapshot.t) (kvs_ordered : List KeyValue.t)
        (history : List snap),
       "latest" ∷ s.[cache.v3.store.t, go!"latest"] ↦ snapshot ∗
       "latest_tree" ∷ own_BTree snapshot.tree' is_kvItem less_kvItem (kvs_ordered.map Sum.inr)
         (DFrac.own q) ∗
       "history" ∷ own_ringBuffer (s.[cache.v3.store.t, go!"history"])
         is_snapshotItem rev_snapshotItem history ∗
       "Hrev" ∷ mono_nat_auth_own γstore.latest_rev_gn 1 (sint.nat snapshot.rev') ∗
       "#Hhistory" ∷ (∀ (revision : w64) (i : Nat) (s : snap),
           ⌜history[i]? = some s ∧
             (sint.Z s.1 ≤ sint.Z revision ∧
              (match history[i + 1]? with
               | some next => sint.Z revision < sint.Z next.1
               | none => sint.Z revision ≤ sint.Z snapshot.rev'))⌝ →
           is_etcd_kvs revision «prefix» (ordered_kvs_to_map s.2)))) ∗
  "_" ∷ True)

set_option maxHeartbeats 1600000 in
theorem wp_store__getSnapshot (rev_lb : Nat) (s : loc) (γstore : store_names) (rev : w64)
    («prefix» : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ "Hs" ∷ own_store s γstore «prefix» ∗
        "#Hlb" ∷ mono_nat_lb_own γstore.latest_rev_gn rev_lb }}
      (App (Val (s @!! go.type.PointerType cache.v3.store @!! go!"getSnapshot")) (Val #rev))
    {{ (snap_ptr : loc) (latest_rev : w64) (err : error.t),
        RET (PairV (PairV #snap_ptr #latest_rev) #err);
        own_store s γstore «prefix» ∗
        match err with
        | interface.nil =>
            (∃ (kvs : List KeyValue.t) (snap_rev : w64),
              is_snapshotItem snap_ptr (snap_rev, kvs) ∗
              ∃ (rev' : w64),
                ⌜if rev = W64 0 then rev_lb ≤ sint.nat rev' else rev' = rev⌝ ∗
                is_etcd_kvs rev' «prefix» (ordered_kvs_to_map kvs))
        | _ => iprop(True) }} := by
  wp_start as ⟨Hs, #Hlb⟩
  wp_apply wp_with_defer as %defer defer
  iNamed Hs
  unfold own_store
  iNamed Hs
  wp_apply sync.wp_RWMutex__RLock $$ [$Hmu] as ⟨Hrlocked, Hown⟩
  icases Hown with ⟨%snapshot, %kvs_ordered, %history, Hown⟩
  iNamed Hown
  wp_auto
  wp_if_destruct
  · ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg $$ []
    · iPkgInit
    ihave #Hi := is_init_access $$ Hpkg
    icases Hi with ⟨%err_not_ready, #HErr⟩
    wp_auto
    wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
    · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
    wp_end
  wp_if_destruct
  · wp_apply wp_slice_literal (V := interface.t) [interface.mk_ok go.int64 #rev]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply fmt.wp_Errorf $$ [$Hsl] as %err -
    wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
    · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
    wp_end
  have Hrev_nn : 0 ≤ sint.Z rev := by word
  wp_bind (If _ _ _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = execute_val⌝ ∗
      rev_ptr ↦ (if rev = W64 0 then snapshot.rev' else rev) ∗
      s.[cache.v3.store.t, go!"latest"] ↦ snapshot ∗ s_ptr ↦ s))) $$ [rev latest s]
  · wp_if_destruct
    · try simp only [↓reduceIte]
      iframe
    · try simp only [Hif, ↓reduceIte]
      iframe
  iintro %v ⟨%Hv, rev, latest, s⟩
  subst Hv
  wp_auto
  generalize hr : (if rev = W64 0 then snapshot.rev' else rev) = r
  wp_if_destruct
  · ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
    · iPkgInit
    ihave #Hi := is_rpctypes_init_access $$ Hpkg
    icases Hi with ⟨%e1, %e2, #HErr1, #HErr2⟩
    wp_auto
    wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
    · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
    wp_end
  rw [show ∀ (x : binder) (e : expr), (RecV BAnon x e : val) = #(func.mk BAnon x e) from
    fun _ _ => by rw [go.into_val_unfold func.t]]
  wp_bind (App (App (Val #(methods _ _ _)) (Val _)) (Val _))
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗
      own_ringBuffer (s.[cache.v3.store.t, go!"history"]) is_snapshotItem rev_snapshotItem history ∗
      (targetSnapshot_ptr ↦ (zero_val loc) ∨
       ∃ (item : loc) (itemv : snap), targetSnapshot_ptr ↦ item ∗ is_snapshotItem item itemv ∗
         ⌜(iter_itemvs rev_snapshotItem r history)[0]? = some itemv⌝)))) $$ [history targetSnapshot]
  · iapply wp_ringBuffer__DescendLessOrEqual (T' := loc) (V := snap)
      (is_item := is_snapshotItem) (rev_item := rev_snapshotItem) (buf := history)
      (P := fun i => iprop(⌜i = 0⌝ ∗ targetSnapshot_ptr ↦ (zero_val loc)))
      $$ [history targetSnapshot] [] []
    · isplitr
      · iPkgInit
      iframe
      ipureintro; rfl
    · iintro %i %item %itemv !> %Ψ ⟨⟨%Hi, targetSnapshot⟩, %Hlookup, #Hitem⟩ HΨ
      subst Hi
      wp_auto
      iapply HΨ
      simp only [Bool.false_eq_true, ↓reduceIte]
      iintro history
      iframe
      iright
      iexists item, itemv
      iframe # ∗
      ipureintro; exact Hlookup
    · iintro history ⟨%_, targetSnapshot⟩
      iframe
      ipureintro; rfl
  iintro %v ⟨%Hv, history, Ht⟩
  subst Hv
  icases Ht with (targetSnapshot | ⟨%item, %itemv, targetSnapshot, #Hitem, %Hlookup⟩)
  · wp_auto
    ihave #Hpkg : is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
    · iPkgInit
    ihave #Hi := is_rpctypes_init_access $$ Hpkg
    icases Hi with ⟨%e1, %e2, #HErr1, #HErr2⟩
    wp_auto
    wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
    · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
    wp_end
  · ihave %Hnn : ⌜item ≠ null⌝ $$ []
    · unfold is_snapshotItem
      icases Hitem with ⟨%tree, #Hsnap, -⟩
      iapply typed_pointsto_not_null $$ Hsnap
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    ihave %Hle := mono_nat_lb_own_valid $$ Hrev Hlb
    wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
    · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
    rcases itemv with ⟨srev, skvs⟩
    obtain ⟨i, Hi, Hp, Hlater⟩ := filter_reverse_head _ _ _ Hlookup
    simp only [rev_snapshotItem] at Hp
    have Hp' := of_decide_eq_true Hp
    iapply HΦ
    isplitl [Hmu]
    · iframe
    dsimp only
    iexists skvs, srev
    iframe #
    iexists r
    isplitr
    · ipureintro
      by_cases h0 : rev = W64 0
      · simp only [h0, ↓reduceIte] at hr ⊢
        subst hr
        exact Hle.2
      · simp only [h0, ↓reduceIte] at hr ⊢
        exact hr.symm
    iapply Hhistory $$ %r %i %(srev, skvs)
    ipureintro
    refine ⟨Hi, Hp', ?_⟩
    rcases hnext : history[i + 1]? with _ | next
    · dsimp only; omega
    · dsimp only
      have := Hlater (i + 1) next (by omega) hnext
      simp only [rev_snapshotItem] at this
      have := of_decide_eq_false this
      omega

theorem wp_store__LatestRev (s : loc) (γstore : store_names) («prefix» : go_string) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_store s γstore «prefix» }}
      (App (Val (s @!! go.type.PointerType cache.v3.store @!! go!"LatestRev")) (Val #()))
    {{ (r : w64), RET #r; own_store s γstore «prefix» }} := by
  wp_start as Hs
  wp_apply wp_with_defer as %defer defer
  unfold own_store
  iNamed Hs
  wp_apply sync.wp_RWMutex__RLock $$ [$Hmu] as ⟨Hrlocked, Hown⟩
  icases Hown with ⟨%snapshot, %kvs_ordered, %history, Hown⟩
  iNamed Hown
  wp_auto
  wp_apply sync.wp_RWMutex__RUnlock $$ [$Hrlocked latest latest_tree history Hrev] as Hmu
  · inext; iexists snapshot, kvs_ordered, history; iframe # ∗
  wp_end

def own_Cache (c_ptr : loc) : IProp GF :=
  iprop(∃ (c : cache.v3.Cache.t) (γstore : store_names),
    "c" ∷ c_ptr ↦ c ∗
    "store" ∷ own_store c.store' γstore c.prefix')

/-- Lean addition: specs of the methods that `Cache.Get` calls but that goose does
not translate (`Perennial/Code/go_etcd_io/etcd/cache/v3.toml` does not list
`Cache.WaitReady`, `Cache.validateGet`, `Cache.serverRevision`,
`Cache.waitTillRevision` and `store.Get`, so `cache.v3.Assumptions` has no
`MethodUnfold` for them and a call of one has no semantics). `wp_Cache__Get` takes
them as a hypothesis instead of axioms. Each spec only asks for the cache's (or
store's) representation predicate and gives it back, with an arbitrary result; the
`Cache` methods are stated over `own_Cache`. -/
structure Cache_Get_callee_specs : Prop where
  wp_Cache__WaitReady : ∀ (c : loc) (ctx : interface.t),
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Cache c }}
      (App (Val (c @!! go.type.PointerType cache.v3.Cache @!! go!"WaitReady")) (Val #ctx))
    {{ (err : error.t), RET #err; own_Cache c }}
  wp_Cache__validateGet : ∀ (c : loc) (key : go_string) (op : client.v3.Op.t)
      (req : RangeRequest.t),
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Cache c ∗ is_Op op (.Get req) }}
      (App (App (Val (c @!! go.type.PointerType cache.v3.Cache @!! go!"validateGet")) (Val #key))
        (Val #op))
    {{ (pred : func.t) (err : error.t), RET (PairV #pred #err); own_Cache c }}
  wp_Cache__serverRevision : ∀ (c : loc) (ctx : interface.t),
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Cache c }}
      (App (Val (c @!! go.type.PointerType cache.v3.Cache @!! go!"serverRevision")) (Val #ctx))
    {{ (rev : w64) (err : error.t), RET (PairV #rev #err); own_Cache c }}
  wp_Cache__waitTillRevision : ∀ (c : loc) (ctx : interface.t) (rev : w64),
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_Cache c }}
      (App (App (Val (c @!! go.type.PointerType cache.v3.Cache @!! go!"waitTillRevision"))
        (Val #ctx)) (Val #rev))
    {{ (err : error.t), RET #err; own_Cache c }}
  wp_store__Get : ∀ (s : loc) (γstore : store_names) («prefix» : go_string)
      (start_sl end_sl : slice.t) (start_key end_key : List w8) (rev : w64),
    {{ is_pkg_init (PROP := IProp GF) pkg ∗ own_store s γstore «prefix» ∗
        start_sl ↦*□ start_key ∗ end_sl ↦*□ end_key }}
      (App (App (App (Val (s @!! go.type.PointerType cache.v3.store @!! go!"Get")) (Val #start_sl))
        (Val #end_sl)) (Val #rev))
    {{ (kvs : slice.t) (latest_rev : w64) (err : error.t),
        RET (PairV (PairV #kvs #latest_rev) #err); own_store s γstore «prefix» }}

/-- Lean deviations from Rocq: the precondition also asks that every option in `opts`
satisfies the client-supplied `is_OpOptions opts pfx fk` (not both `WithPrefix` and
`WithFromKey`: else `OpGet` panics), and the theorem takes the specs of the
untranslated callees (`Cache_Get_callee_specs`) as a hypothesis. -/
theorem wp_Cache__Get (Hspecs : Cache_Get_callee_specs (GF := GF))
    (c : loc) (ctx : interface.t) (key : go_string) (opts_sl : slice.t)
    (opts : List client.v3.OpOption.t) (pfx fk : Bool) (Hpfx_fk : ¬ (pfx = true ∧ fk = true)) :
    {{ is_pkg_init (PROP := IProp GF) pkg ∗
        "opts_sl" ∷ opts_sl ↦* opts ∗
        "#Hopts" ∷ is_OpOptions opts pfx fk ∗
        "cache" ∷ own_Cache c }}
      (App (App (App (Val (c @!! go.type.PointerType cache.v3.Cache @!! go!"Get")) (Val #ctx))
        (Val #key)) (Val #opts_sl))
    {{ (resp : loc) (err : error.t), RET (PairV #resp #err); True }} := by
  wp_start as ⟨opts_sl, #Hopts, cache⟩
  unfold own_Cache
  icases cache with ⟨%cv, %γ, Hc, Hstore⟩
  wp_auto
  wp_apply wp_store__LatestRev $$ [$Hstore] as %r Hstore
  ihave cache : own_Cache c $$ [Hc Hstore]
  · unfold own_Cache; iexists cv, γ; iframe
  -- `if c.store.LatestRev() == 0 { if err := c.WaitReady(ctx); err != nil { return nil, err } }`
  wp_join (Q := fun v => iprop((⌜v = execute_val⌝ ∗ own_Cache c ∗ c_ptr ↦ c ∗ ctx_ptr ↦ ctx) ∨
      ∃ (resp : loc) (err : error.t), ⌜v = return_val (PairV #resp #err)⌝)) with [cache c ctx]
  · wp_apply (Hspecs.wp_Cache__WaitReady c ctx) $$ [$cache] as %err cache
    cases err
    · wp_auto
      iright; iexists _, _; ipureintro; rfl
    · wp_auto
      ileft; iframe
      ipureintro; rfl
  · ileft; iframe
  iintro HQ
  icases HQ with (⟨%Hv, cache, c, ctx⟩ | ⟨%resp, %err, %Hv⟩)
  · subst Hv
    wp_auto
    wp_apply wp_OpGet_opts key opts_sl opts (DFrac.own 1) pfx fk Hpfx_fk $$ [$opts_sl $Hopts]
      as %op %req ⟨opts_sl, #Hop⟩
    wp_apply (Hspecs.wp_Cache__validateGet c key op req) $$ [$cache $Hop] as %pred %err cache
    cases err
    · wp_auto
      wp_end
    wp_auto
    wp_apply wp_string_to_bytes as %start_sl ⟨start_sl, -⟩
    ipersist start_sl
    -- `op.RangeBytes()`, `op.Rev()`, `op.IsSerializable()` (pointer and value methods)
    iterate 6
      wp_method_call
      wp_call
      wp_auto
    -- `if !op.IsSerializable() { ... }`
    wp_join (Q := fun v => iprop((⌜v = execute_val⌝ ∗ own_Cache c ∗ c_ptr ↦ c ∗
          requestedRev_ptr ↦ op.rev') ∨
        ∃ (resp : loc) (err : error.t), ⌜v = return_val (PairV #resp #err)⌝)) at next
        with [cache c ctx requestedRev]
    · cases op.serializable'
      case' true =>
        wp_auto
        ileft; iframe
        ipureintro; rfl
      wp_auto
      wp_apply (Hspecs.wp_Cache__serverRevision c ctx) $$ [$cache] as %srev %err cache
      cases err
      · wp_auto
        iright; iexists _, _; ipureintro; rfl
      wp_auto
      wp_if_destruct
      · ihave #Hpkg' : is_pkg_init (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.v3rpc.rpctypes $$ []
        · iPkgInit
        ihave #Hi := is_rpctypes_init_access $$ Hpkg'
        icases Hi with ⟨%e1, %e2, #HErr1, #HErr2⟩
        wp_auto
        iright; iexists _, _; ipureintro; rfl
      wp_apply (Hspecs.wp_Cache__waitTillRevision c ctx srev) $$ [$cache] as %err cache
      cases err
      · wp_auto
        iright; iexists _, _; ipureintro; rfl
      · wp_auto
        ileft; iframe
        ipureintro; rfl
    iintro HQ
    icases HQ with (⟨%Hv, cache, c, requestedRev⟩ | ⟨%resp, %err, %Hv⟩)
    · subst Hv
      wp_auto
      -- `kvs, latestRev, err := c.store.Get(startKey, endKey, requestedRev)`
      unfold own_Cache
      icases cache with ⟨%cv', %γ', Hc, Hstore⟩
      ihave #Hend : op.end' ↦*□ req.range_end $$ [Hop]
      · simp only [is_Op_unseal, is_Op_def, is_Op_RangeRequest]
        icases Hop with ⟨-, -, Hend, -⟩
        iexact Hend
      wp_auto
      wp_apply (Hspecs.wp_store__Get cv'.store' γ' cv'.prefix' start_sl op.end' key req.range_end
        op.rev') $$ [$Hstore $start_sl $Hend] as %kvs_sl %latest_rev %err Hstore
      cases err
      · wp_auto
        wp_end
      wp_auto
      wp_alloc resp as Hresp
      wp_end
    · subst Hv
      wp_auto
      wp_end
  · subst Hv
    wp_auto
    wp_end

end store

end go_etcd_io.etcd.cache.v3_proof

end Perennial
end
