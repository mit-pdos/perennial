From iris.algebra.lib Require Import mono_nat mono_list gmap_view.
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
Local Definition tsR := gmap_viewR nat (leibnizO unit).
Local Definition ts_modsR := gmap_viewR (nat * dbmap) (leibnizO unit).
Local Definition dbmapR := gmap_viewR u64 (leibnizO dbval).

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
    (* tuple *)
    mvcc_ptupleG :> inG Σ key_vchainR;
    mvcc_ltupleG :> inG Σ key_vchainR;
    (* GC *)
    mvcc_sid_tidsG :> inG Σ sid_tidsR;
    mvcc_sid_min_tidG :> inG Σ sid_min_tidR;
    (* SST *)
    mvcc_tsG :> inG Σ mono_natR;
    mvcc_abort_tids_ncaG :> inG Σ tsR;
    mvcc_abort_tids_faG :> inG Σ tsR;
    mvcc_abort_tids_fciG :> inG Σ ts_modsR;
    mvcc_abort_tids_fccG :> inG Σ ts_modsR;
    mvcc_commit_tidsG :> inG Σ ts_modsR;
    mvcc_dbmapG :> inG Σ dbmapR;
  }.

Definition mvcc_ghostΣ :=
  #[
     GFunctor key_vchainR;
     GFunctor key_vchainR;
     GFunctor sid_tidsR;
     GFunctor sid_min_tidR;
     GFunctor mono_natR;
     GFunctor tsR;
     GFunctor tsR;
     GFunctor ts_modsR;
     GFunctor ts_modsR;
     GFunctor ts_modsR;
     GFunctor dbmapR
   ].

Global Instance subG_mvcc_ghostG {Σ} :
  subG mvcc_ghostΣ Σ → mvcc_ghostG Σ.
Proof. solve_inG. Qed.

Record mvcc_names :=
  {
    mvcc_ptuple : gname;
    mvcc_ltuple : gname;
    mvcc_sid_tids : gname;
    mvcc_sid_min_tid : gname;
    mvcc_ts : gname;
    mvcc_abort_tids_nca : gname;
    mvcc_abort_tids_fa : gname;
    mvcc_abort_tmods_fci : gname;
    mvcc_abort_tmods_fcc : gname;
    mvcc_cmt_tmods : gname;
    mvcc_dbmap : gname
  }.

(* Per-txn ghost state. *)
Class mvcc_txn_ghostG Σ :=
  {
    mvcc_txnmapG :> inG Σ dbmapR;
  }.

Definition mvcc_txn_ghostΣ :=
  #[
     GFunctor dbmapR
   ].

Global Instance subG_mvcc_txn_ghostG {Σ} :
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
  own γ.(mvcc_ts) (●MN ts).

Definition ts_lb γ (ts : nat) : iProp Σ :=
  own γ.(mvcc_ts) (◯MN ts).

Definition nca_tids_auth γ (tids : gset nat) : iProp Σ :=
  own γ.(mvcc_abort_tids_nca) (gmap_view_auth (V:=leibnizO unit) (DfracOwn 1) (gset_to_gmap tt tids)).

Definition nca_tids_frag γ (tid : nat) : iProp Σ :=
  own γ.(mvcc_abort_tids_nca) (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt).

Definition fa_tids_auth γ (tids : gset nat) : iProp Σ :=
  own γ.(mvcc_abort_tids_fa) (gmap_view_auth (V:=leibnizO unit) (DfracOwn 1) (gset_to_gmap tt tids)).

Definition fa_tids_frag γ (tid : nat) : iProp Σ :=
  own γ.(mvcc_abort_tids_fa) (gmap_view_frag (V:=leibnizO unit) tid (DfracOwn 1) tt).

Definition fci_tmods_auth γ tmods : iProp Σ :=
  own γ.(mvcc_abort_tmods_fci) (gmap_view_auth (V:=leibnizO unit) (DfracOwn 1) (gset_to_gmap tt tmods)).

Definition fci_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  own γ.(mvcc_abort_tmods_fci) (gmap_view_frag (V:=leibnizO unit) tmod (DfracOwn 1) tt).

Definition fcc_tmods_auth γ tmods : iProp Σ :=
  own γ.(mvcc_abort_tmods_fcc) (gmap_view_auth (V:=leibnizO unit) (DfracOwn 1) (gset_to_gmap tt tmods)).

Definition fcc_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  own γ.(mvcc_abort_tmods_fcc) (gmap_view_frag (V:=leibnizO unit) tmod (DfracOwn 1) tt).

Definition cmt_tmods_auth γ tmods : iProp Σ :=
  own γ.(mvcc_cmt_tmods) (gmap_view_auth (V:=leibnizO unit) (DfracOwn 1) (gset_to_gmap tt tmods)).

Definition cmt_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  own γ.(mvcc_cmt_tmods) (gmap_view_frag (V:=leibnizO unit) tmod (DfracOwn 1) tt).

Definition dbmap_auth γ m : iProp Σ :=
  own γ.(mvcc_dbmap) (gmap_view_auth (DfracOwn 1) m).

Definition dbmap_ptsto γ k q v : iProp Σ :=
  own γ.(mvcc_dbmap) (gmap_view_frag k (DfracOwn q) v).

Definition dbmap_ptstos γ q (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, dbmap_ptsto γ k q v.

(* Definitions about per-txn resources. *)
Definition txnmap_auth τ m : iProp Σ :=
  own τ (gmap_view_auth (DfracOwn 1) m).

Definition txnmap_ptsto τ k v : iProp Σ :=
  own τ (gmap_view_frag k (DfracOwn 1) v).

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
Admitted.

Lemma ts_lb_weaken {γ ts} ts' :
  (ts' ≤ ts)%nat ->
  ts_lb γ ts -∗
  ts_lb γ ts'.
Admitted.

Lemma ts_auth_lb_le {γ ts ts'} :
  ts_auth γ ts -∗
  ts_lb γ ts' -∗
  ⌜(ts' ≤ ts)%nat⌝.
Admitted.

Lemma ts_lb_zero γ :
  ⊢ |==> ts_lb γ 0%nat.
Admitted.

Lemma mvcc_ghost_init :
  ⊢ |==> ∃ γ, ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
              ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
              ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
              ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
              ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0) ∗
              ([∗ list] sid ∈ sids_all, site_min_tid_half_auth γ sid 0).
Admitted.

Lemma dbmap_lookup_big {γ q m} m' :
  dbmap_auth γ m -∗
  dbmap_ptstos γ q m' -∗
  ⌜m' ⊆ m⌝.
Admitted.

Lemma dbmap_update_big {γ q m} m0 m1 :
  dom m0 = dom m1 →
  dbmap_auth γ m -∗
  dbmap_ptstos γ q m0 ==∗
  dbmap_auth γ (m1 ∪ m) ∗
  dbmap_ptstos γ q m1.
Admitted.

Lemma dbmap_elem_split {γ k q} q1 q2 v :
  (q1 + q2 = q)%Qp ->
  dbmap_ptsto γ k q v -∗
  dbmap_ptsto γ k q1 v ∗
  dbmap_ptsto γ k q2 v.
Admitted.

Lemma dbmap_elem_combine {γ k} q1 q2 v1 v2 :
  dbmap_ptsto γ k q1 v1 -∗
  dbmap_ptsto γ k q2 v2 -∗
  dbmap_ptsto γ k (q2 + q2) v1 ∗
  ⌜v1 = v2⌝.
Admitted.

Lemma txnmap_lookup τ m k v :
  txnmap_auth τ m -∗
  txnmap_ptsto τ k v -∗
  ⌜m !! k = Some v⌝.
Admitted.

Lemma txnmap_lookup_big τ m m' :
  txnmap_auth τ m -∗
  txnmap_ptstos τ m' -∗
  ⌜m' ⊆ m⌝.
Admitted.

Lemma txnmap_update {τ m k v} w :
  txnmap_auth τ m -∗
  txnmap_ptsto τ k v ==∗
  txnmap_auth τ (<[ k := w ]> m) ∗
  txnmap_ptsto τ k w.
Admitted.

Lemma txnmap_alloc m :
  ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
Admitted.

Lemma nca_tids_insert {γ tids} tid :
  tid ∉ tids ->
  nca_tids_auth γ tids ==∗
  nca_tids_auth γ ({[ tid ]} ∪ tids) ∗ nca_tids_frag γ tid.
Admitted.

Lemma nca_tids_delete {γ tids} tid :
  nca_tids_frag γ tid -∗
  nca_tids_auth γ tids ==∗
  nca_tids_auth γ (tids ∖ {[ tid ]}).
Admitted.

Lemma nca_tids_lookup {γ tids} tid :
  nca_tids_frag γ tid -∗
  nca_tids_auth γ tids -∗
  ⌜tid ∈ tids⌝.
Admitted.

Lemma fa_tids_insert {γ tids} tid :
  tid ∉ tids ->
  fa_tids_auth γ tids ==∗
  fa_tids_auth γ ({[ tid ]} ∪ tids) ∗ fa_tids_frag γ tid.
Admitted.

Lemma fa_tids_delete {γ tids} tid :
  fa_tids_frag γ tid -∗
  fa_tids_auth γ tids ==∗
  fa_tids_auth γ (tids ∖ {[ tid ]}).
Admitted.

Lemma fa_tids_lookup {γ tids} tid :
  fa_tids_frag γ tid -∗
  fa_tids_auth γ tids -∗
  ⌜tid ∈ tids⌝.
Admitted.

Lemma fci_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  fci_tmods_auth γ tmods ==∗
  fci_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ fci_tmods_frag γ tmod.
Admitted.

Lemma fci_tmods_delete {γ tmods} tmod :
  fci_tmods_frag γ tmod -∗
  fci_tmods_auth γ tmods ==∗
  fci_tmods_auth γ (tmods ∖ {[ tmod ]}).
Admitted.

Lemma fci_tmods_lookup {γ tmods} tmod :
  fci_tmods_frag γ tmod -∗
  fci_tmods_auth γ tmods -∗
  ⌜tmod ∈ tmods⌝.
Admitted.

Lemma fcc_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  fcc_tmods_auth γ tmods ==∗
  fcc_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ fcc_tmods_frag γ tmod.
Admitted.

Lemma fcc_tmods_delete {γ tmods} tmod :
  fcc_tmods_frag γ tmod -∗
  fcc_tmods_auth γ tmods ==∗
  fcc_tmods_auth γ (tmods ∖ {[ tmod ]}).
Admitted.

Lemma fcc_tmods_lookup {γ tmods} tmod :
  fcc_tmods_frag γ tmod -∗
  fcc_tmods_auth γ tmods -∗
  ⌜tmod ∈ tmods⌝.
Admitted.

Lemma cmt_tmods_insert {γ tmods} tmod :
  tmod ∉ tmods ->
  cmt_tmods_auth γ tmods ==∗
  cmt_tmods_auth γ ({[ tmod ]} ∪ tmods) ∗ cmt_tmods_frag γ tmod.
Admitted.

Lemma cmt_tmods_delete {γ tmods} tmod :
  cmt_tmods_frag γ tmod -∗
  cmt_tmods_auth γ tmods ==∗
  cmt_tmods_auth γ (tmods ∖ {[ tmod ]}).
Admitted.

Lemma cmt_tmods_lookup {γ tmods} tmod :
  cmt_tmods_frag γ tmod -∗
  cmt_tmods_auth γ tmods -∗
  ⌜tmod ∈ tmods⌝.
Admitted.

End lemmas.
