From iris.algebra.lib Require Import mono_nat mono_list gmap_view.
From Perennial.base_logic Require Import ghost_map mono_nat.
From Perennial.program_proof.mvcc Require Import mvcc_prelude.

(* Tuple-related RAs. *)
Local Definition vchainR := mono_listR (leibnizO dbval).
Local Definition key_vchainR := gmapR u64 vchainR.
(* GC-related RAs. *)
Local Definition tidsR := gmap_viewR u64 (leibnizO unit).
Local Definition sid_tidsR := gmapR u64 tidsR.
Local Definition sid_min_tidR := gmapR u64 mono_natR.
(* SST-related RAs. (SST = Strictly Serializable Transactions) *)
(* TODO: See if we can make [tidsR] used by GC also [tsR]. *)
(*
Local Definition tsR := gmap_viewR nat (leibnizO unit).
Local Definition ts_modsR := gmap_viewR (nat * dbmap) (leibnizO unit).
Local Definition dbmapR := gmap_viewR u64 (leibnizO dbval).
 *)


Lemma sids_all_lookup (sid : u64) :
  int.Z sid < N_TXN_SITES ->
  sids_all !! (int.nat sid) = Some sid.
Proof.
  intros H.
  unfold sids_all.
  rewrite list_lookup_fmap.
  rewrite lookup_seqZ_lt; last word.
  simpl. f_equal. word.
Qed.

(* Global ghost states. *)
Class mvcc_ghostG Σ :=
  {
    (* SST *)
    mvcc_ptupleG :> inG Σ key_vchainR;
    mvcc_ltupleG :> inG Σ key_vchainR;
    mvcc_tsG :> mono_natG Σ;
    mvcc_abort_tids_ncaG :> ghost_mapG Σ nat unit;
    mvcc_abort_tids_faG :> ghost_mapG Σ nat unit;
    mvcc_abort_tids_fciG :> ghost_mapG Σ (nat * dbmap) unit;
    mvcc_abort_tids_fccG :> ghost_mapG Σ (nat * dbmap) unit;
    mvcc_commit_tidsG :> ghost_mapG Σ (nat * dbmap) unit;
    mvcc_dbmapG :> ghost_mapG Σ u64 dbval;
    (* GC *)
    mvcc_sid_tidsG :> inG Σ sid_tidsR;
    mvcc_sid_min_tidG :> inG Σ sid_min_tidR;
  }.

Definition mvcc_ghostΣ :=
  #[
     GFunctor key_vchainR;
     GFunctor key_vchainR;
     mono_natΣ;
     ghost_mapΣ nat unit;
     ghost_mapΣ nat unit;
     ghost_mapΣ (nat * dbmap) unit;
     ghost_mapΣ (nat * dbmap) unit;
     ghost_mapΣ (nat * dbmap) unit;
     ghost_mapΣ u64 dbval;
     GFunctor sid_tidsR;
     GFunctor sid_min_tidR
   ].

#[global]
Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

Record mvcc_names :=
  {
    mvcc_ptuple : gname;
    mvcc_ltuple : gname;
    mvcc_ts : gname;
    mvcc_abort_tids_nca : gname;
    mvcc_abort_tids_fa : gname;
    mvcc_abort_tmods_fci : gname;
    mvcc_abort_tmods_fcc : gname;
    mvcc_cmt_tmods : gname;
    mvcc_dbmap : gname;
    mvcc_sid_tids : gname;
    mvcc_sid_min_tid : gname
  }.

(* Per-txn ghost state. *)
Class mvcc_txn_ghostG Σ :=
  {
    mvcc_txnmapG :> ghost_mapG Σ u64 dbval;
  }.

Definition mvcc_txn_ghostΣ :=
  #[
     ghost_mapΣ u64 dbval
   ].

#[global]
Instance subG_mvcc_txn_ghostG {Σ} :
  subG mvcc_txn_ghostΣ Σ → mvcc_txn_ghostG Σ.
Proof. solve_inG. Qed.


Section definitions.
Context `{!mvcc_ghostG Σ}.

Definition ptuple_auth γ q (k : u64) (phys : list dbval) : iProp Σ :=
  own γ.(mvcc_ptuple) {[k := ●ML{# q } (phys : list (leibnizO dbval))]}.

Definition ptuple_lb γ (k : u64) (phys : list dbval) : iProp Σ :=
  own γ.(mvcc_ptuple) {[k := ◯ML (phys : list (leibnizO dbval))]}.

Definition ltuple_auth γ (k : u64) (logi : list dbval) : iProp Σ :=
  own γ.(mvcc_ltuple) {[k := ●ML (logi : list (leibnizO dbval))]}.

Definition ltuple_lb γ (k : u64) (logi : list dbval) : iProp Σ :=
  own γ.(mvcc_ltuple) {[k := ◯ML (logi : list (leibnizO dbval))]}.

(* TODO: use nat rather than u64 for tid. *)
Definition ptuple_ptsto γ (k : u64) (v : dbval) (ts : nat) : iProp Σ :=
  ∃ phys, ptuple_lb γ k phys ∗ ⌜phys !! ts = Some v⌝.

Definition mods_token γ (k : u64) (ts : nat) : iProp Σ :=
  ∃ phys, ptuple_auth γ (1/4) k phys ∗ ⌜(length phys ≤ S ts)%nat⌝.

Definition ltuple_ptsto γ (k : u64) (v : dbval) (ts : nat) : iProp Σ :=
  ∃ logi, ltuple_lb γ k logi ∗ ⌜logi !! ts = Some v⌝.

Definition ltuple_ptstos γ (m : dbmap) (ts : nat) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, ltuple_ptsto γ k v ts.

(* Definitions about GC-related resources. *)
Definition site_active_tids_half_auth γ (sid : u64) tids : iProp Σ :=
  own γ.(mvcc_sid_tids) {[sid := (gmap_view_auth (DfracOwn (1 / 2)) tids)]}.

Definition site_active_tids_frag γ (sid : u64) tid : iProp Σ :=
  own γ.(mvcc_sid_tids) {[sid := (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt)]}.

Definition active_tid γ (tid sid : u64) : iProp Σ :=
  (site_active_tids_frag γ sid tid ∧ ⌜int.Z sid < N_TXN_SITES⌝) ∧ ⌜0 < int.Z tid < 2 ^ 64 - 1⌝ .

Definition site_min_tid_half_auth γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid) {[sid := (●MN{#(1 / 2)} tidN)]}.

Definition site_min_tid_lb γ (sid : u64) tidN : iProp Σ :=
  own γ.(mvcc_sid_min_tid) {[sid := (◯MN tidN)]}.

Definition min_tid_lb γ tidN : iProp Σ :=
  [∗ list] sid ∈ sids_all, site_min_tid_lb γ sid tidN.

(* Definitions about SST-related resources. *)
Definition ts_auth γ (ts : nat) : iProp Σ :=
  mono_nat_auth_own γ.(mvcc_ts) 1 ts.

Definition ts_lb γ (ts : nat) : iProp Σ :=
  mono_nat_lb_own γ.(mvcc_ts) ts.

Definition nca_tids_auth γ (tids : gset nat) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tids_nca) 1 (gset_to_gmap tt tids).

Definition nca_tids_frag γ (tid : nat) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tids_nca) tid (DfracOwn 1) tt.

Definition fa_tids_auth γ (tids : gset nat) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tids_fa) 1 (gset_to_gmap tt tids).

Definition fa_tids_frag γ (tid : nat) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tids_fa) tid (DfracOwn 1) tt.

Definition fci_tmods_auth γ tmods : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tmods_fci) 1 (gset_to_gmap tt tmods).

Definition fci_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tmods_fci) tmod (DfracOwn 1) tt.

Definition fcc_tmods_auth γ tmods : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tmods_fcc) 1 (gset_to_gmap tt tmods).

Definition fcc_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tmods_fcc) tmod (DfracOwn 1) tt.

Definition cmt_tmods_auth γ tmods : iProp Σ :=
  ghost_map_auth γ.(mvcc_cmt_tmods) 1 (gset_to_gmap tt tmods).

Definition cmt_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_cmt_tmods) tmod (DfracOwn 1) tt.

Definition dbmap_auth γ m : iProp Σ :=
  ghost_map_auth γ.(mvcc_dbmap) 1 m.

Definition dbmap_ptsto γ k q v : iProp Σ :=
  ghost_map_elem γ.(mvcc_dbmap) k (DfracOwn q) v.

Definition dbmap_ptstos γ q (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, dbmap_ptsto γ k q v.

(* Definitions about per-txn resources. *)
Definition txnmap_auth τ m : iProp Σ :=
  ghost_map_auth τ 1 m.

Definition txnmap_ptsto τ k v : iProp Σ :=
  ghost_map_elem τ k (DfracOwn 1) v.

Definition txnmap_ptstos τ (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v.

End definitions.

Section lemmas.
Context `{!heapGS Σ, !mvcc_ghostG Σ}.

(* TODO: Renmae [vchain_] to [ptuple_] *)
Lemma vchain_combine {γ} q {q1 q2 key vchain1 vchain2} :
  (q1 + q2 = q)%Qp ->
  ptuple_auth γ q1 key vchain1 -∗
  ptuple_auth γ q2 key vchain2 -∗
  ptuple_auth γ q key vchain1 ∧ ⌜vchain2 = vchain1⌝.
Proof.
  iIntros "%Hq Hv1 Hv2".
  iCombine "Hv1 Hv2" as "Hv".
  iDestruct (own_valid with "Hv") as %Hvalid.
  rewrite singleton_valid mono_list_auth_dfrac_op_valid_L in Hvalid.
  destruct Hvalid as [_ <-].
  rewrite -mono_list_auth_dfrac_op dfrac_op_own Hq.
  naive_solver.
Qed.

Lemma vchain_split {γ q} q1 q2 {key vchain} :
  (q1 + q2 = q)%Qp ->
  ptuple_auth γ q key vchain -∗
  ptuple_auth γ q1 key vchain ∗ ptuple_auth γ q2 key vchain.
Proof.
  iIntros "%Hq Hv".
  unfold ptuple_auth.
  rewrite -Hq.
  rewrite -dfrac_op_own.
  (* rewrite mono_list_auth_dfrac_op. *)
Admitted.

Lemma vchain_witness γ q k vchain :
  ptuple_auth γ q k vchain -∗ ptuple_lb γ k vchain.
Proof.
  iApply own_mono.
  apply singleton_mono, mono_list_included.
Qed.

Lemma ptuple_prefix γ q k l l' :
  ptuple_auth γ q k l -∗
  ptuple_lb γ k l' -∗
  ⌜prefix l' l⌝.
Proof.
  iIntros "Hl Hl'".
  iDestruct (own_valid_2 with "Hl Hl'") as %Hval.
  iPureIntro. revert Hval.
  rewrite singleton_op singleton_valid.
  rewrite mono_list_both_dfrac_valid_L.
  by intros [_ H].
Qed.

Lemma vchain_update {γ key vchain} vchain' :
  prefix vchain vchain' →
  ptuple_auth γ (1 / 2) key vchain -∗
  ptuple_auth γ (1 / 2) key vchain ==∗
  ptuple_auth γ (1 / 2) key vchain' ∗ ptuple_auth γ (1 / 2) key vchain'.
Proof.
Admitted.

Lemma vchain_false {γ q key vchain} :
  (1 < q)%Qp ->
  ptuple_auth γ q key vchain -∗
  False.
Proof.
Admitted.

Lemma ptuple_agree {γ q1 q2 key vchain1 vchain2} :
  ptuple_auth γ q1 key vchain1 -∗
  ptuple_auth γ q2 key vchain2 -∗
  ⌜vchain1 = vchain2⌝.
Admitted.

Lemma ltuple_update {γ key l} l' :
  prefix l l' →
  ltuple_auth γ key l ==∗
  ltuple_auth γ key l'.
Proof.
Admitted.

Lemma ltuple_witness γ k l :
  ltuple_auth γ k l -∗ ltuple_lb γ k l.
Proof.
  iApply own_mono.
  apply singleton_mono, mono_list_included.
Qed.

Lemma ltuple_prefix γ k l l' :
  ltuple_auth γ k l -∗
  ltuple_lb γ k l' -∗
  ⌜prefix l' l⌝.
Proof.
  iIntros "Hl Hl'".
  iDestruct (own_valid_2 with "Hl Hl'") as %Hval.
  iPureIntro. revert Hval.
  rewrite singleton_op singleton_valid.
  by rewrite mono_list_both_valid_L.
Qed.

Lemma site_active_tids_elem_of γ (sid : u64) tids tid :
  site_active_tids_half_auth γ sid tids -∗ site_active_tids_frag γ sid tid -∗ ⌜tid ∈ (dom tids)⌝.
Admitted.

Lemma site_active_tids_agree γ (sid : u64) tids tids' :
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids' -∗
  ⌜tids = tids'⌝.
Admitted.

Lemma site_active_tids_insert {γ sid tids} tid :
  tid ∉ dom tids ->
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_half_auth γ sid (<[tid := tt]>tids) ∗
  site_active_tids_frag γ sid tid.
Admitted.

Lemma site_active_tids_delete {γ sid tids} tid :
  site_active_tids_frag γ sid tid -∗
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (delete tid tids) ∗
  site_active_tids_half_auth γ sid (delete tid tids). 
Admitted.

Lemma site_min_tid_valid γ (sid : u64) tidN tidlbN :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidlbN -∗
  ⌜(tidlbN ≤ tidN)%nat⌝.
Admitted.

Lemma site_min_tid_lb_weaken γ (sid : u64) tidN tidN' :
  (tidN' ≤ tidN)%nat ->
  site_min_tid_lb γ sid tidN -∗
  site_min_tid_lb γ sid tidN'.
Admitted.

Lemma site_min_tid_agree γ (sid : u64) tidN tidN' :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN' -∗
  ⌜tidN = tidN'⌝.
Admitted.

Lemma site_min_tid_update {γ sid tidN} tidN' :
  (tidN ≤ tidN')%nat ->
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_half_auth γ sid tidN ==∗
  site_min_tid_half_auth γ sid tidN' ∗ site_min_tid_half_auth γ sid tidN'.
Admitted.

Lemma site_min_tid_witness {γ sid tidN} :
  site_min_tid_half_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidN.
Admitted.

Lemma min_tid_lb_zero γ :
  ⊢ |==> min_tid_lb γ 0%nat.
Admitted.

Lemma ts_witness {γ ts} :
  ts_auth γ ts -∗
  ts_lb γ ts.
Proof. iApply mono_nat_lb_own_get. Qed.

Lemma ts_lb_weaken {γ ts} ts' :
  (ts' ≤ ts)%nat ->
  ts_lb γ ts -∗
  ts_lb γ ts'.
Proof. iIntros "%Hle Hlb". iApply mono_nat_lb_own_le; done. Qed.

Lemma ts_auth_lb_le {γ ts ts'} :
  ts_auth γ ts -∗
  ts_lb γ ts' -∗
  ⌜(ts' ≤ ts)%nat⌝.
Proof.
  iIntros "Hauth Hlb".
  iDestruct (mono_nat_lb_own_valid with "Hauth Hlb") as %[_ Hle].
  done.
Qed.

Lemma mvcc_ghost_alloc :
  ⊢ |==> ∃ γ,
    (* SST-related. *)
    ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
    ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
    ([∗ set] key ∈ keys_all, ltuple_auth γ key [Nil; Nil]) ∗
    ts_auth γ 0%nat ∗
    nca_tids_auth γ ∅ ∗
    fa_tids_auth γ ∅ ∗
    fci_tmods_auth γ ∅ ∗
    fcc_tmods_auth γ ∅ ∗
    cmt_tmods_auth γ ∅ ∗
    dbmap_auth γ ∅ ∗
    (* GC-related. *)
    ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
    ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
    ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0) ∗
    ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0).
Admitted.

(**
 * Lemma [ghost_map_lookup_big] is not helpful here since we want to
 * specify the fraction of fragmentary elements.
 *)
Lemma dbmap_lookup_big {γ q m} m' :
  dbmap_auth γ m -∗
  dbmap_ptstos γ q m' -∗
  ⌜m' ⊆ m⌝.
Proof.
  iIntros "Hauth Hpts". rewrite map_subseteq_spec. iIntros (k v Hm0).
  iDestruct (ghost_map_lookup with "Hauth [Hpts]") as %->.
  { rewrite /dbmap_ptstos big_sepM_lookup; done. }
  done.
Qed.

Lemma dbmap_update_big {γ m} m0 m1 :
  dom m0 = dom m1 →
  dbmap_auth γ m -∗
  dbmap_ptstos γ 1 m0 ==∗
  dbmap_auth γ (m1 ∪ m) ∗
  dbmap_ptstos γ 1 m1.
Proof.
  iIntros "%Hdom Hauth Hpts".
  iApply (ghost_map_update_big with "Hauth Hpts").
  done.
Qed.

Lemma dbmap_elem_split {γ k q} q1 q2 v :
  (q1 + q2 = q)%Qp ->
  dbmap_ptsto γ k q v -∗
  dbmap_ptsto γ k q1 v ∗
  dbmap_ptsto γ k q2 v.
Proof.
  iIntros "%Hq Hpt". subst q.
  iDestruct "Hpt" as "[Hpt1 Hpt2]".
  iFrame.
Qed.

Lemma dbmap_elem_combine {γ k} q1 q2 v1 v2 :
  dbmap_ptsto γ k q1 v1 -∗
  dbmap_ptsto γ k q2 v2 -∗
  dbmap_ptsto γ k (q1 + q2) v1 ∗
  ⌜v1 = v2⌝.
Proof.
  iIntros "Hpt1 Hpt2".
  iDestruct (ghost_map_elem_combine with "Hpt1 Hpt2") as "[Hpt %Eqv]".
  rewrite dfrac_op_own.
  by iFrame.
Qed.

Lemma txnmap_lookup τ m k v :
  txnmap_auth τ m -∗
  txnmap_ptsto τ k v -∗
  ⌜m !! k = Some v⌝.
Proof. iApply ghost_map_lookup. Qed.

Lemma txnmap_lookup_big τ m m' :
  txnmap_auth τ m -∗
  txnmap_ptstos τ m' -∗
  ⌜m' ⊆ m⌝.
Proof. iApply ghost_map_lookup_big. Qed.

Lemma txnmap_update {τ m k v} w :
  txnmap_auth τ m -∗
  txnmap_ptsto τ k v ==∗
  txnmap_auth τ (<[ k := w ]> m) ∗
  txnmap_ptsto τ k w.
Proof. iApply ghost_map_update. Qed.

Lemma txnmap_alloc m :
  ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
Proof. iApply ghost_map_alloc. Qed.

Lemma nca_tids_insert {γ tids} tid :
  tid ∉ tids ->
  nca_tids_auth γ tids ==∗
  nca_tids_auth γ ({[ tid ]} ∪ tids) ∗ nca_tids_frag γ tid.
Proof.
  iIntros "%Hnotin Hauth".
  unfold nca_tids_auth.
  rewrite gset_to_gmap_union_singleton.
  iApply (ghost_map_insert with "Hauth").
  rewrite lookup_gset_to_gmap_None.
  done.
Qed.

Lemma nca_tids_delete {γ tids} tid :
  nca_tids_auth γ tids -∗
  nca_tids_frag γ tid ==∗
  nca_tids_auth γ (tids ∖ {[ tid ]}).
Proof.
  iIntros "Hauth Helem".
  unfold nca_tids_auth.
  rewrite gset_to_gmap_difference_singleton.
  iApply (ghost_map_delete with "Hauth Helem").
Qed.

Lemma nca_tids_lookup {γ tids} tid :
  nca_tids_auth γ tids -∗
  nca_tids_frag γ tid -∗
  ⌜tid ∈ tids⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  done.
Qed.

Lemma fa_tids_insert {γ tids} tid :
  tid ∉ tids ->
  fa_tids_auth γ tids ==∗
  fa_tids_auth γ ({[ tid ]} ∪ tids) ∗ fa_tids_frag γ tid.
Proof.
  iIntros "%Hnotin Hauth".
  unfold fa_tids_auth.
  rewrite gset_to_gmap_union_singleton.
  iApply (ghost_map_insert with "Hauth").
  rewrite lookup_gset_to_gmap_None.
  done.
Qed.

Lemma fa_tids_delete {γ tids} tid :
  fa_tids_auth γ tids -∗
  fa_tids_frag γ tid ==∗
  fa_tids_auth γ (tids ∖ {[ tid ]}).
Proof.
  iIntros "Hauth Helem".
  unfold fa_tids_auth.
  rewrite gset_to_gmap_difference_singleton.
  iApply (ghost_map_delete with "Hauth Helem").
Qed.

Lemma fa_tids_lookup {γ tids} tid :
  fa_tids_auth γ tids -∗
  fa_tids_frag γ tid -∗
  ⌜tid ∈ tids⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  done.
Qed.

Lemma fci_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  fci_tmods_auth γ tmods ==∗
  fci_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ fci_tmods_frag γ tmod.
Proof.
  iIntros "%Hnotin Hauth".
  unfold fci_tmods_auth.
  rewrite gset_to_gmap_union_singleton.
  iApply (ghost_map_insert with "Hauth").
  rewrite lookup_gset_to_gmap_None.
  done.
Qed.

Lemma fci_tmods_delete {γ tmods} tmod :
  fci_tmods_auth γ tmods -∗
  fci_tmods_frag γ tmod ==∗
  fci_tmods_auth γ (tmods ∖ {[ tmod ]}).
Proof.
  iIntros "Hauth Helem".
  unfold fci_tmods_auth.
  rewrite gset_to_gmap_difference_singleton.
  iApply (ghost_map_delete with "Hauth Helem").
Qed.

Lemma fci_tmods_lookup {γ tmods} tmod :
  fci_tmods_auth γ tmods -∗
  fci_tmods_frag γ tmod -∗
  ⌜tmod ∈ tmods⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  done.
Qed.

Lemma fcc_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  fcc_tmods_auth γ tmods ==∗
  fcc_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ fcc_tmods_frag γ tmod.
Proof.
  iIntros "%Hnotin Hauth".
  unfold fcc_tmods_auth.
  rewrite gset_to_gmap_union_singleton.
  iApply (ghost_map_insert with "Hauth").
  rewrite lookup_gset_to_gmap_None.
  done.
Qed.

Lemma fcc_tmods_delete {γ tmods} tmod :
  fcc_tmods_auth γ tmods -∗
  fcc_tmods_frag γ tmod ==∗
  fcc_tmods_auth γ (tmods ∖ {[ tmod ]}).
Proof.
  iIntros "Hauth Helem".
  unfold fcc_tmods_auth.
  rewrite gset_to_gmap_difference_singleton.
  iApply (ghost_map_delete with "Hauth Helem").
Qed.

Lemma fcc_tmods_lookup {γ tmods} tmod :
  fcc_tmods_auth γ tmods -∗
  fcc_tmods_frag γ tmod -∗
  ⌜tmod ∈ tmods⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  done.
Qed.

Lemma cmt_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  cmt_tmods_auth γ tmods ==∗
  cmt_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ cmt_tmods_frag γ tmod.
Proof.
  iIntros "%Hnotin Hauth".
  unfold cmt_tmods_auth.
  rewrite gset_to_gmap_union_singleton.
  iApply (ghost_map_insert with "Hauth").
  rewrite lookup_gset_to_gmap_None.
  done.
Qed.

Lemma cmt_tmods_delete {γ tmods} tmod :
  cmt_tmods_auth γ tmods -∗
  cmt_tmods_frag γ tmod ==∗
  cmt_tmods_auth γ (tmods ∖ {[ tmod ]}).
Proof.
  iIntros "Hauth Helem".
  unfold cmt_tmods_auth.
  rewrite gset_to_gmap_difference_singleton.
  iApply (ghost_map_delete with "Hauth Helem").
Qed.

Lemma cmt_tmods_lookup {γ tmods} tmod :
  cmt_tmods_auth γ tmods -∗
  cmt_tmods_frag γ tmod -∗
  ⌜tmod ∈ tmods⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (ghost_map_lookup with "Hauth Helem") as "%Hlookup".
  apply lookup_gset_to_gmap_Some in Hlookup as [Helem _].
  done.
Qed.

End lemmas.

(**
 * Consider using Typeclass Opaque to improve performance.
 *)
