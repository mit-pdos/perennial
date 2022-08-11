From iris.algebra Require Import dfrac_agree.
From iris.algebra.lib Require Import mono_nat mono_list gmap_view.
From Perennial.program_proof Require Import grove_prelude.

Definition dbval := option u64.
Notation Nil := (None : dbval).
Notation Value x := (Some x : dbval).

Definition to_dbval (b : bool) (v : u64) :=
  if b then Value v else Nil.

Definition dbmap := gmap u64 dbval.

Definition N_TXN_SITES : Z := 64.

Definition keys_all : gset u64 := fin_to_set u64.
Definition sids_all : list u64 := U64 <$> seqZ 0 N_TXN_SITES.

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

Section action.

Inductive action :=
| EvCommit (tid : nat) (mods : dbmap)
| EvRead   (tid : nat) (key : u64)
| EvAbort  (tid : nat).

Definition head_commit (l : list action) (tid : nat) (mods : dbmap) :=
  head l = Some (EvCommit tid mods).

Definition head_read (l : list action) (tid : nat) (key : u64) :=
  head l = Some (EvRead tid key).

Definition head_abort (l : list action) (tid : nat) :=
  head l = Some (EvAbort tid).

Definition no_commit_abort (l : list action) (tid : nat) :=
  (∀ mods, EvCommit tid mods ∉ l) ∧
  (EvAbort tid ∉ l).

Definition first_abort (l : list action) (tid : nat) :=
  ∃ lp ls,
    l = lp ++ (EvAbort tid) :: ls ∧
    no_commit_abort lp tid.

Definition compatible (tid : nat) (mods : dbmap) (e : action) :=
  match e with
  | EvCommit tid' mods' => (tid' < tid)%nat ∨ (dom mods) ∩ (dom mods') = ∅
  | EvRead tid' key => (tid' ≤ tid)%nat ∨ key ∉ (dom mods)
  | EvAbort tid' => True
  end.

Instance compatible_dec tid mods e : Decision (compatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition incompatible (tid : nat) (mods : dbmap) (e : action) := not (compatible tid mods e).

Instance incompatible_dec tid mods e : Decision (incompatible tid mods e).
Proof. destruct e; simpl; apply _. Defined.

Definition compatible_all (l : list action) (tid : nat) (mods : dbmap) :=
  Forall (compatible tid mods) l.

Definition incompatible_exists (l : list action) (tid : nat) (mods : dbmap) :=
  Exists (incompatible tid mods) l.

Definition first_commit (l lp ls : list action) (tid : nat) (mods : dbmap) :=
  l = lp ++ (EvCommit tid mods) :: ls ∧
  no_commit_abort lp tid.

Definition first_commit_incompatible (l1 l2 : list action) (tid : nat) (mods : dbmap) :=
  ∃ lp ls,
    first_commit l2 lp ls tid mods ∧
    incompatible_exists (l1 ++ lp) tid mods.

Definition first_commit_compatible (l : list action) (tid : nat) (mods : dbmap) :=
  ∃ lp ls,
    first_commit l lp ls tid mods ∧
    compatible_all lp tid mods.

Definition is_commit_abort_tid (tid : nat) (e : action) : Prop :=
  match e with
  | EvCommit tid' _ => tid = tid'
  | EvAbort tid' => tid = tid'
  | _ => False
  end.

Instance is_commit_abort_dec tid e : Decision (is_commit_abort_tid tid e).
Proof. destruct e; simpl; apply _. Defined.

Lemma is_commit_abort_tid_lor tid e :
  is_commit_abort_tid tid e ->
  (∃ mods, e = EvCommit tid mods) ∨ e = EvAbort tid.
Proof. intros. destruct e; set_solver. Qed.

Fixpoint find_max_prefix (tid : nat) (lp ls : list action) : (list action * list action) :=
  match ls with
  | [] => (lp, ls)
  | hd :: tl => if decide (is_commit_abort_tid tid hd)
              then (lp, ls)
              else find_max_prefix tid (lp ++ [hd]) tl
  end.

Lemma spec_find_max_prefix tid lp ls :
  ∃ ls1 ls2,
    (lp ++ ls1, ls2) = find_max_prefix tid lp ls ∧
    ls = ls1 ++ ls2 ∧
    no_commit_abort ls1 tid ∧
    (match head ls2 with
     | Some e => is_commit_abort_tid tid e
     | _ => True
     end).
Proof.
  generalize dependent lp.
  unfold no_commit_abort.
  induction ls as [| e ls IHls]; intros lp; simpl.
  - exists [], [].
    split; first by rewrite app_nil_r.
    set_solver.
  - case_decide.
    + exists [], (e :: ls).
      split; first by rewrite app_nil_r.
      set_solver.
    + destruct (IHls (lp ++ [e])) as (ls1 & ls2 & Heq & Hls2 & Hnca & Hhead).
      exists ([e] ++ ls1), ls2.
      rewrite -Heq.
      split; first by rewrite app_assoc.
      split; set_solver.
Qed.

Inductive tcform :=
| NCA
| FA
| FCI (mods : dbmap)
| FCC (mods : dbmap).

Definition peek (l : list action) (tid : nat) : tcform :=
  let (lp, ls) := find_max_prefix tid [] l
  in match head ls with
     | None => NCA
     | Some e => match e with
                | EvCommit _ mods => if decide (compatible_all lp tid mods) then FCC mods else FCI mods
                | _ => FA
                end
     end.

Theorem spec_peek l tid :
  match peek l tid with
  | NCA => no_commit_abort l tid
  | FA => first_abort l tid
  | FCI mods => first_commit_incompatible [] l tid mods
  | FCC mods => first_commit_compatible l tid mods
  end.
Proof.
  unfold peek.
  destruct (spec_find_max_prefix tid [] l) as (lp & ls & Hspec & Hl & Hnca & Hls).
  rewrite -Hspec.
  destruct (head ls) eqn:Els.
  - destruct a eqn:Ee.
    + simpl.
      apply is_commit_abort_tid_lor in Hls.
      destruct Hls as [[mods' Hls] | Hls]; last set_solver.
      inversion Hls. subst tid0 mods'.
      assert (Hfc : first_commit l lp (tail ls) tid mods).
      { unfold first_commit.
        split; last done.
        rewrite Hl.
        f_equal.
        by apply hd_error_tl_repr.
      }
      case_decide.
      * unfold first_commit_compatible.
        by exists lp, (tail ls).
      * unfold first_commit_incompatible.
        exists lp, (tail ls).
        unfold compatible_all in H.
        by apply not_Forall_Exists in H; last apply _.
    + unfold is_commit_abort_tid in Hls. set_solver.
    + apply is_commit_abort_tid_lor in Hls.
      destruct Hls; first set_solver.
      inversion H. subst tid0.
      unfold first_abort.
      exists lp, (tail ls).
      split; last done.
      rewrite Hl.
      f_equal.
      by apply hd_error_tl_repr.
  - apply head_None in Els.
    rewrite Els in Hl. rewrite app_nil_r in Hl. by rewrite Hl.
Qed.

Lemma no_commit_abort_false {l : list action} {tid : nat} :
  no_commit_abort l tid ->
  (∃ mods, head_commit l tid mods) ∨ (head_abort l tid) ->
  False.
Proof.
  intros [HnotinC HnotinA] [[mods Hhead] | Hhead]; apply head_Some_elem_of in Hhead; set_solver.
Qed.

Lemma head_middle {X} (l lp ls : list X) (x : X) :
  l = lp ++ x :: ls ->
  head l = head (lp ++ [x]).
Proof.
  intros Hl. rewrite Hl. destruct lp; auto.
Qed.

Theorem first_abort_false {l : list action} {tid : nat} (mods : dbmap) :
  first_abort l tid ->
  head_commit l tid mods ->
  False.
Proof.
  intros (lp & ls & Hl & HnotinC & _) Hhead.
  unfold head_commit in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Theorem first_commit_false {l lp ls : list action} {tid : nat} {mods : dbmap} :
  first_commit l lp ls tid mods ->
  head_abort l tid ->
  False.
Proof.
  intros (Hl & _ & HnotinA) Hhead.
  unfold head_abort in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  apply head_Some_elem_of in Hhead.
  set_solver.
Qed.

Theorem first_commit_eq {l lp ls : list action} {tid : nat} {mods mods' : dbmap} :
  first_commit l lp ls tid mods ->
  head_commit l tid mods' ->
  mods = mods'.
Proof.
  intros (Hl & HnotinC & _) Hhead.
  unfold head_commit in Hhead.
  destruct lp; set_solver.
Qed.

Theorem safe_extension_rd (l : list action) (tid tid' : nat) (mods : dbmap) (key : u64) :
  first_commit_compatible l tid mods ->
  head_read l tid' key ->
  key ∈ (dom mods) ->
  (tid' ≤ tid)%nat.
Proof.
  intros (lp & ls & [Hl _] & Hcomp) Hhead Hin.
  unfold head_read in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  destruct lp; first set_solver.
  simpl in Hhead.
  inversion Hhead.
  unfold compatible_all in Hcomp.
  rewrite Forall_forall in Hcomp.
  destruct (Hcomp (EvRead tid' key)); [| done | done].
  rewrite H0.
  apply elem_of_list_here.
Qed.

Theorem safe_extension_wr (l : list action) (tid tid' : nat) (mods mods' : dbmap) :
  first_commit_compatible l tid mods ->
  head_commit l tid' mods' ->
  (dom mods) ∩ (dom mods') ≠ ∅ ->
  (tid' ≤ tid)%nat.
Proof.
  intros (lp & ls & [Hl _] & Hcomp) Hhead Hdom.
  unfold head_commit in Hhead.
  rewrite (head_middle _ _ _ _ Hl) in Hhead.
  destruct lp; first set_solver.
  simpl in Hhead.
  inversion Hhead.
  unfold compatible_all in Hcomp.
  rewrite Forall_forall in Hcomp.
  destruct (Hcomp (EvCommit tid' mods')); [| word | done].
  rewrite H0.
  apply elem_of_list_here.
Qed.

Lemma first_commit_incompatible_Exists (l1 l2 : list action) (tid : nat) (mods : dbmap) :
  first_commit_incompatible l1 l2 tid mods ->
  head_commit l2 tid mods ->
  Exists (incompatible tid mods) l1.
Proof.
  intros (lp & ls & [Hl [HnotinC _]] & Hincomp) Hhead.
  destruct lp; first by rewrite app_nil_r in Hincomp.
  unfold head_commit in Hhead.
  set_solver.
Qed.

Lemma Exists_incompatible_exists (l : list action) (tid : nat) (mods : dbmap) :
  Exists (incompatible tid mods) l ->
  ∃ key tid', key ∈ dom mods ∧
    ((EvRead tid' key ∈ l ∧ (tid < tid')%nat) ∨
     (∃ mods', key ∈ dom mods' ∧ EvCommit tid' mods' ∈ l ∧ (tid ≤ tid')%nat)).
Proof.
  intros H.
  rewrite Exists_exists in H.
  destruct H as (a & Helem & Hincomp).
  unfold incompatible, compatible in Hincomp.
  destruct a as [tid' mods' | tid' key |] eqn:E; last done.
  - (* Case Evcommit. *)
    apply Decidable.not_or in Hincomp.
    destruct Hincomp as [Hle Hoverlap].
    assert (Hindom : ∃ key, key ∈ dom mods ∧ key ∈ dom mods').
    { apply set_choose_L in Hoverlap. set_solver. }
    destruct Hindom as (key & Hindom & Hindom').
    eauto 10 with lia.
  - (* Case EvRead. *)
    apply Decidable.not_or in Hincomp.
    destruct Hincomp as [Hlt Hindom].
    apply dec_stable in Hindom.
    eauto 10 with lia.
Qed.

Lemma notin_tail {X} (x : X) (l : list X) :
  x ∉ l ->
  x ∉ tail l.
Proof.
  intros Hnotin.
  destruct l; first done.
  intros contra. simpl in contra. set_solver.
Qed.

Lemma no_commit_abort_preserved (l l' : list action) {tid : nat} :
  l' = tail l ->
  no_commit_abort l tid ->
  no_commit_abort l' tid.
Proof.
  intros Htl [Hnc Hna].
  rewrite Htl.
  unfold no_commit_abort in *.
  split.
  - intros mods. by apply notin_tail.
  - by apply notin_tail.
Qed.
  
Lemma first_abort_preserved {l l' : list action} {a : action} {tid : nat} :
  l = a :: l' ->
  a ≠ EvAbort tid ->
  first_abort l tid ->
  first_abort l' tid.
Proof.
  intros Hhead Hneq Hfa.
  destruct Hfa as (lp & ls & [Hl [HnotinC HnotinA]]).
  exists (tail lp), ls.
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Lemma first_commit_incompatible_preserved {p l l' : list action} {a : action} {tid : nat} {mods : dbmap} :
  l = a :: l' ->
  (∀ mods', a ≠ EvCommit tid mods') ->
  first_commit_incompatible p l tid mods ->
  first_commit_incompatible (p ++ [a]) l' tid mods.
Proof.
  intros Hhead Hneq Hfci.
  destruct Hfci as (lp & ls & [Hl [HnotinC HnotinA]] & Hincomp).
  exists (tail lp), ls.
  split; last first.
  { rewrite -app_assoc.
    simpl.
    replace (a :: tail lp) with lp; first done.
    destruct lp eqn:Elp; first set_solver.
    simpl.
    rewrite -hd_error_tl_repr in Hhead.
    destruct Hhead as [Hhead _].
    set_solver.
  }
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  unfold first_commit.
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Lemma first_commit_compatible_preserved {l l' : list action} {a : action} {tid : nat} {mods : dbmap} :
  l = a :: l' ->
  (∀ mods', a ≠ EvCommit tid mods') ->
  first_commit_compatible l tid mods ->
  first_commit_compatible l' tid mods.
Proof.
  intros Hhead Hneq Hfcc.
  destruct Hfcc as (lp & ls & [Hl [HnotinC HnotinA]] & Hcomp).
  exists (tail lp), ls.
  split; last by apply Forall_tail.
  split; last first.
  { unfold no_commit_abort.
    split; last by apply notin_tail.
    intros mods'. by apply notin_tail.
  }
  unfold first_commit.
  destruct lp eqn:Elp; first set_solver.
  simpl.
  rewrite -hd_error_tl_repr in Hhead.
  destruct Hhead as [_ Hl'].
  by rewrite -Hl' Hl.
Qed.

Theorem first_commit_incompatible_suffix (l1 l2 : list action) (tid : nat) (mods : dbmap) :
  first_commit_incompatible [] l2 tid mods ->
  first_commit_incompatible l1 l2 tid mods.
Proof.
  intros Hfci.
  unfold first_commit_incompatible in *.
  destruct Hfci as (lp & ls & Hfc & Hincomp).
  exists lp, ls.
  split; first auto.
  simpl in Hincomp.
  apply Exists_app. by right.
Qed.

End action.

Section tuplext.

(**
 * Convert global modifications to per-tuple modification.
 *)
Fixpoint per_tuple_mods_list (l : list (nat * dbmap)) (key : u64) : gset (nat * dbval) :=
  match l with
  | [] => ∅
  | hd :: tl => match hd.2 !! key with
              | None => per_tuple_mods_list tl key
              | Some v => {[ (hd.1, v) ]} ∪ (per_tuple_mods_list tl key)
              end
  end.

Definition per_tuple_mods (s : gset (nat * dbmap)) (key : u64) : gset (nat * dbval) :=
  per_tuple_mods_list (elements s) key.

(* TODO: Rename lemma names from [mods] to [tmods], [tuple] to [key]. *)

Lemma mods_tuple_to_global_list l key tid v :
  (tid, v) ∈ per_tuple_mods_list l key ->
  ∃ mods, (tid, mods) ∈ l ∧ mods !! key = Some v.
Proof.
  intros H.
  induction l as [| x l IHl]; first set_solver.
  simpl in H.
  destruct (x.2 !! key) eqn:E.
  - rewrite elem_of_union in H.
    destruct H; last set_solver.
    rewrite elem_of_singleton in H.
    inversion H.
    subst tid d.
    exists x.2.
    rewrite -(surjective_pairing x).
    set_solver.
  - destruct (IHl H) as [mods [Hin Hlookup]].
    set_solver.
Qed.

Lemma mods_tuple_to_global s key tid v :
  (tid, v) ∈ per_tuple_mods s key ->
  ∃ mods, (tid, mods) ∈ s ∧ mods !! key = Some v.
Proof.
  intros H.
  apply mods_tuple_to_global_list in H.
  set_solver.
Qed.

Lemma mods_global_to_tuple_list l key tid mods v :
  (tid, mods) ∈ l ∧ mods !! key = Some v ->
  (tid, v) ∈ per_tuple_mods_list l key.
Proof.
  intros [Helem Hlookup].
  induction l as [| x l IHl]; first set_solver.
  rewrite elem_of_cons in Helem.
  destruct Helem.
  - subst x. simpl.
    rewrite Hlookup.
    set_solver.
  - specialize (IHl H). simpl.
    destruct (x.2 !! key); set_solver.
Qed.

Lemma mods_global_to_tuple {s key tid} mods {v} :
  (tid, mods) ∈ s ∧ mods !! key = Some v ->
  (tid, v) ∈ per_tuple_mods s key. 
Proof.
  intros [Helem Hlookup].
  rewrite -elem_of_elements in Helem.
  by apply mods_global_to_tuple_list with mods.
Qed.

Lemma tmods_NoDup_notin_difference {tmods : gset (nat * dbmap)} {tid mods} :
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  ∀ m, (tid, m) ∉ tmods ∖ {[ (tid, mods) ]}.
Proof.
  intros HND Helem m Helem'.
  apply union_difference_singleton_L in Helem.
  set tmods' := tmods ∖ {[ (tid, mods) ]} in Helem Helem'.
  rewrite Helem in HND.
  rewrite fmap_Permutation in HND; last first.
  { apply elements_union_singleton. set_solver. }
  simpl in HND.
  apply NoDup_cons_1_1 in HND.
  set_solver.
Qed.

Lemma per_tuple_mods_union_None
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} :
  mods !! k = None ->
  per_tuple_mods ({[ (tid, mods) ]} ∪ tmods) k = per_tuple_mods tmods k.
Proof.
  intros Hlookup.
  rewrite set_eq.
  intros [t v].
  split.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    rewrite elem_of_union in Helem.
    destruct Helem; first set_solver.
    by apply mods_global_to_tuple with mods'.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    apply mods_global_to_tuple with mods'.
    split; [set_solver | done].
Qed.

Lemma per_tuple_mods_union_Some
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} (v : dbval) :
  mods !! k = Some v ->
  per_tuple_mods ({[ (tid, mods) ]} ∪ tmods) k = {[ (tid, v) ]} ∪ (per_tuple_mods tmods k).
Proof.
  intros Hlookup.
  rewrite set_eq.
  intros [t u].
  split.
  - intros Helem.
    apply mods_tuple_to_global in Helem.
    destruct Helem as (mods' & Helem & Hlookup').
    rewrite elem_of_union in Helem.
    destruct Helem; first set_solver.
    rewrite elem_of_union. right.
    by apply mods_global_to_tuple with mods'.
  - intros Helem.
    rewrite elem_of_union in Helem.
    destruct Helem.
    + rewrite elem_of_singleton in H. rewrite H.
      apply mods_global_to_tuple with mods.
      split; [set_solver | done].
    + apply mods_tuple_to_global in H.
      destruct H as (mods' & Helem & Hlookup').
      apply mods_global_to_tuple with mods'.
      split; [set_solver | done].
Qed.

Lemma per_tuple_mods_minus_None
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} :
  mods !! k = None ->
  per_tuple_mods (tmods ∖ {[ (tid, mods) ]}) k = per_tuple_mods tmods k.
Proof.
  intros Hlookup.
  destruct (decide ((tid, mods) ∈ tmods)); last first.
  { by replace (_ ∖ _) with tmods by set_solver. }
  rewrite {2} (union_difference_L {[ (tid, mods) ]} tmods); last set_solver.
  set tmods' := _ ∖ _.
  symmetry.
  by apply per_tuple_mods_union_None.
Qed.

Lemma tmods_global_to_key_notin {tmods : gset (nat * dbmap)} {tid : nat} k v :
  (∀ mods, (tid, mods) ∉ tmods) ->
  (tid, v) ∉ per_tuple_mods tmods k.
Proof.
  intros Hnotin Helem.
  apply mods_tuple_to_global in Helem.
  destruct Helem as (mods & Helem & _).
  set_solver.
Qed.

Lemma per_tuple_mods_minus_Some
      {tmods : gset (nat * dbmap)} {tid : nat} {mods : dbmap} {k : u64} (v : dbval) :
  NoDup (elements tmods).*1 ->
  (tid, mods) ∈ tmods ->
  mods !! k = Some v ->
  per_tuple_mods (tmods ∖ {[ (tid, mods) ]}) k = (per_tuple_mods tmods k) ∖ {[ (tid, v) ]}.
Proof.
  intros HND Helem Hlookup.
  rewrite {2} (union_difference_L {[ (tid, mods) ]} tmods); last set_solver.
  set tmods' := _ ∖ _.
  pose proof (tmods_NoDup_notin_difference HND Helem) as Hnotin.
  apply (tmods_global_to_key_notin k v) in Hnotin.
  rewrite (per_tuple_mods_union_Some v); [set_solver | done].
Qed.

Definition find_tid_val_step (tid : nat) (x : nat * dbval) (res : (option nat) * dbval)
  : (option nat) * dbval :=
  match res.1 with
  | None => if decide (x.1 < tid) then (Some x.1, x.2) else res
  | Some tid' => if decide (tid' < x.1 < tid) then (Some x.1, x.2) else res
  end.

Lemma find_tid_val_step_noop tid x res :
  (tid ≤ x.1)%nat ->
  find_tid_val_step tid x res = res.
Proof.
  intros Hle.
  unfold find_tid_val_step.
  destruct res.1 eqn:E.
  - case_decide; [lia | done].
  - case_decide; [lia | done].
Qed.
  
Definition find_tid_val (tid : nat) (v : dbval) (l : list (nat * dbval)) : (option nat) * dbval :=
  foldr (find_tid_val_step tid) (None, v) l.

Lemma find_tid_val_unfold tid v l :
  find_tid_val tid v l = foldr (find_tid_val_step tid) (None, v) l.
Proof. reflexivity. Qed.

Definition find_val tid v l := (find_tid_val tid v l).2.

Definition imme_pred (l : list nat) (p n : nat) :=
  p ∈ l ∧ (p < n)%nat ∧ Forall (λ x, x ≤ p ∨ n ≤ x)%nat l.

Lemma find_tid_val_spec tid v l :
  let res := find_tid_val tid v l in
  match res.1 with
  | None => Forall (λ x, tid ≤ x)%nat l.*1 ∧ res.2 = v
  | Some tid' => imme_pred l.*1 tid' tid ∧ (tid', res.2) ∈ l
  end.
Proof.
  induction l as [| x l IHl].
  - by simpl.
  - simpl in IHl.
    destruct (find_tid_val _ _ l).1 eqn:E.
    + unfold find_tid_val. simpl.
      unfold find_tid_val_step. rewrite E.
      case_decide.
      * simpl.
        destruct IHl as [(Helem & Hlt & Hl) _].
        split; last first.
        { rewrite -(surjective_pairing x). set_solver. }
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ Hl).
        lia.
      * rewrite E.
        destruct IHl as [(Helem & Hlt & Hl) Helem'].
        split; last set_solver.
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ Hl).
        lia.
    + unfold find_tid_val. simpl.
      unfold find_tid_val_step. rewrite E.
      case_decide.
      * simpl.
        split; last first.
        { rewrite -(surjective_pairing x). set_solver. }
        split; first set_solver.
        split; first lia.
        apply Forall_cons.
        split; first lia.
        destruct IHl as [IHl _].
        apply (Forall_impl _ _ _ IHl).
        lia.
      * rewrite E.
        destruct IHl as [IHl Heq].
        split; last auto.
        apply Forall_cons.
        split; first lia.
        apply (Forall_impl _ _ _ IHl).
        lia.
Qed.

Lemma find_tid_val_Some tid d l :
  Exists (λ x, x.1 < tid)%nat l ->
  ∃ tid' v', find_tid_val tid d l = (Some tid', v') ∧ imme_pred l.*1 tid' tid ∧ (tid', v') ∈ l.
Proof.
  intros HExists.
  rewrite Exists_exists in HExists.
  destruct HExists as (x & Helem & Hlt).
  pose proof (find_tid_val_spec tid d l) as Hspec. simpl in Hspec.
  destruct (find_tid_val tid d l).1 eqn:E.
  - destruct Hspec as [_ Helem'].
    pose proof (find_tid_val_spec tid d l) as Hspec. simpl in Hspec.
    rewrite E in Hspec.
    set res := (find_tid_val tid d l).
    exists n, res.2.
    split; last auto.
    rewrite (surjective_pairing res).
    by apply pair_equal_spec.
  - destruct Hspec as [Hallge _].
    apply (elem_of_list_fmap_1 fst) in Helem. simpl in Helem.
    rewrite Forall_forall in Hallge.
    apply Hallge in Helem. lia.
Qed.

Lemma find_tid_val_None tid d l :
  Forall (λ x, tid ≤ x.1)%nat l ->
  find_tid_val tid d l = (None, d).
Proof.
  intros HForall.
  induction l as [| x l IHl]; first set_solver.
  rewrite Forall_cons in HForall.
  destruct HForall as [Hx HForall].
  simpl. rewrite IHl; last auto.
  unfold find_tid_val_step. simpl.
  by case_decide; first lia.
Qed.

Lemma find_tid_val_Exists tid d1 d2 l :
  Exists (λ x, x.1 < tid)%nat l ->
  find_tid_val tid d1 l = find_tid_val tid d2 l.
Proof.
  intros HExists.
  induction l as [| x l IHl]; first by apply Exists_nil in HExists.
  simpl.
  apply Exists_cons in HExists.
  destruct HExists.
  - destruct (decide (Forall (λ x, tid ≤ x.1)%nat l)).
    + pose proof (find_tid_val_None _ d1 l f).
      pose proof (find_tid_val_None _ d2 l f).
      rewrite H0 H1.
      unfold find_tid_val_step. simpl.
      by case_decide; last lia.
    + apply not_Forall_Exists in n; last apply _.
      f_equal.
      apply IHl.
      apply (Exists_impl _ _ _ n).
      simpl. lia.
  - f_equal. by apply IHl.
Qed.

Lemma find_tid_val_extensible tid tid' v l :
  Forall (λ x, x.1 < tid')%nat l ->
  (tid' ≤ tid)%nat ->
  find_tid_val tid' v l = find_tid_val tid v l.
Proof.
  intros Hallgt Hle.
  induction l as [| x l IHl]; first done.
  simpl.
  rewrite Forall_cons in Hallgt.
  destruct Hallgt as [Hx Hallgt].
  rewrite IHl; last auto.
  set res := (find_tid_val _ _ _).
  unfold find_tid_val_step.
  destruct res.1.
  - case_decide.
    + case_decide; [done | lia].
    + case_decide; [lia | done].
  - case_decide; last lia.
    case_decide; last lia. done.
Qed.

Lemma imme_pred_perm_eq (p1 p2 n : nat) (l1 l2 : list nat) :
  l1 ≡ₚ l2 ->
  imme_pred l1 p1 n ->
  imme_pred l2 p2 n ->
  p1 = p2.
Proof.
  intros Hperm Hl1 Hl2.
  destruct Hl1 as (Helem1 & Hlt1 & Hl1).
  destruct Hl2 as (Helem2 & Hlt2 & Hl2).
  rewrite elem_of_Permutation_proper in Helem1; last apply Hperm.
  apply Permutation_sym in Hperm.
  rewrite elem_of_Permutation_proper in Helem2; last apply Hperm.
  rewrite Forall_forall in Hl1.
  rewrite Forall_forall in Hl2.
  apply Hl1 in Helem2.
  apply Hl2 in Helem1.
  lia.
Qed.

Lemma NoDup_perm_fmap_fst (l1 l2 : list (nat * dbval)) (a : nat) (b1 b2 : dbval) :
  NoDup l1.*1 ->
  l1 ≡ₚ l2 ->
  (a, b1) ∈ l1 ->
  (a, b2) ∈ l2 ->
  b1 = b2.
Proof.
  intros HNoDup Hperm Helem1 Helem2.
  apply Permutation_sym in Hperm.
  rewrite elem_of_Permutation_proper in Helem2; last apply Hperm.
  (* Funny way to prove this... *)
  pose proof (elem_of_list_to_map_1 _ _ _ HNoDup Helem1) as H1.
  pose proof (elem_of_list_to_map_1 _ _ _ HNoDup Helem2) as H2.
  naive_solver.
Qed.

Lemma NoDup_elements_fmap_fst_union (tid : nat) (v : dbval) (s : gset (nat * dbval)) :
  tid ∉ (elements s).*1 ->
  NoDup (elements s).*1 ->
  NoDup (elements ({[ (tid, v) ]} ∪ s)).*1.
Proof.
  intros Hnotin HNoDup.
  rewrite fmap_Permutation; last first.
  { apply elements_union_singleton.
    intros contra.
    rewrite -elem_of_elements in contra.
    by apply (elem_of_list_fmap_1 fst) in contra.
  }
  rewrite fmap_cons. simpl.
  by apply NoDup_cons_2; last auto.
Qed.

Lemma NoDup_elements_fmap_fst_difference (tid : nat) (v : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  NoDup (elements (s ∖ {[ (tid, v) ]})).*1.
Proof.
  intros HNoDup.
  destruct (decide ((tid, v) ∈ s)); last first.
  { by replace (s ∖ _) with s by set_solver. }
  rewrite (union_difference_singleton_L _ _ e) in HNoDup.
  remember (s ∖ _) as s'.
  rewrite fmap_Permutation in HNoDup; last first.
  { apply elements_union_singleton. set_solver. }
  rewrite fmap_cons NoDup_cons in HNoDup.
  by destruct HNoDup as [_ HNoDup].
Qed.

Lemma find_tid_val_perm tid v l1 l2 :
  NoDup l1.*1 ->
  l1 ≡ₚ l2 ->
  find_tid_val tid v l1 = find_tid_val tid v l2.
Proof.
  intros HNoDup Hperm.
  assert (Hpermfst : l1.*1 ≡ₚ l2.*1) by by apply fmap_Permutation.
  pose proof (find_tid_val_spec tid v l1) as Hl1.
  pose proof (find_tid_val_spec tid v l2) as Hl2.
  simpl in Hl1, Hl2.
  destruct (find_tid_val _ _ l1).1 eqn:E1.
  - destruct (find_tid_val _ _ l2).1 eqn:E2.
    + destruct Hl1 as [Hl1 Helem1].
      destruct Hl2 as [Hl2 Helem2].
      pose proof (imme_pred_perm_eq _ _ _ _ _ Hpermfst Hl1 Hl2) as Heq.
      subst n0.
      rewrite (surjective_pairing (find_tid_val _ _ l1)).
      rewrite (surjective_pairing (find_tid_val _ _ l2)).
      rewrite E1 E2.
      apply pair_equal_spec.
      split; first done.
      apply (NoDup_perm_fmap_fst l1 l2 n); auto.
    + destruct Hl1 as [(Hn & Hlt & _) _].
      destruct Hl2 as [Hl2 _].
      rewrite elem_of_Permutation_proper in Hn; last apply Hpermfst.
      rewrite Forall_forall in Hl2.
      apply Hl2 in Hn. lia.
  - destruct (find_tid_val _ _ l2).1 eqn:E2.
    + destruct Hl2 as [(Hn & Hlt & _) _].
      destruct Hl1 as [Hl1 _].
      apply Permutation_sym in Hpermfst.
      rewrite elem_of_Permutation_proper in Hn; last apply Hpermfst.
      rewrite Forall_forall in Hl1.
      apply Hl1 in Hn. lia.
    + unfold find_val.
      destruct Hl1 as [_ Helem1].
      destruct Hl2 as [_ Helem2].
      rewrite (surjective_pairing (find_tid_val _ _ l1)).
      rewrite (surjective_pairing (find_tid_val _ _ l2)).
      rewrite E1 E2.
      apply pair_equal_spec.
      split; first done.
      by rewrite Helem1 Helem2.
Qed.

Definition diff_tid_val_at (tid : nat) (v : dbval) (s : gset (nat * dbval)) :=
  find_tid_val tid v (elements s).

Lemma diff_tid_val_at_unfold tid v s :
  diff_tid_val_at tid v s = find_tid_val tid v (elements s).
Proof. reflexivity. Qed.

Definition diff_val_at (tid : nat) (v : dbval) (s : gset (nat * dbval)) :=
  (diff_tid_val_at tid v s).2.

Definition le_tids_mods (tid : nat) (mods : gset (nat * dbval)) :=
  set_Forall (λ x, (tid <= x.1)%nat) mods.

Definition gt_tids_mods (tid : nat) (mods : gset (nat * dbval)) :=
  set_Forall (λ x, (x.1 < tid)%nat) mods.

Lemma le_tids_mods_weaken tid tid' mods :
  (tid ≤ tid')%nat ->
  le_tids_mods tid' mods ->
  le_tids_mods tid mods.
Proof. intros Hle H. apply (set_Forall_impl _ _ _ H). lia. Qed.

Lemma gt_tids_mods_Forall_fmap_fst tid mods :
  gt_tids_mods tid mods ->
  Forall (λ n, (n < tid)%nat) (elements mods).*1.
Proof.
  intros H.
  unfold gt_tids_mods in H.
  rewrite set_Forall_elements in H.
  by apply Forall_fmap.
Qed.
                                        
Lemma diff_tid_val_at_le_all tid v s :
  le_tids_mods tid s ->
  diff_tid_val_at tid v s = (None, v).
Proof.
  intros Hle.
  unfold le_tids_mods in Hle. rewrite set_Forall_elements in Hle.
  unfold diff_tid_val_at.
  remember (elements s) as l.
  clear Heql.
  induction l as [| x l IHl]; first auto.
  rewrite Forall_cons in Hle.
  destruct Hle as [Hx Hle].
  apply IHl in Hle.
  unfold find_tid_val.
  simpl.
  unfold find_tid_val in Hle.
  rewrite Hle.
  unfold find_tid_val_step. simpl.
  case_decide; [lia | done].
Qed.

Lemma diff_val_at_le_all tid v s :
  le_tids_mods tid s ->
  diff_val_at tid v s = v.
Proof.
  intros Hle. unfold diff_val_at.
  rewrite diff_tid_val_at_le_all; done.
Qed.

Lemma diff_tid_val_at_S (tid : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  (tid, v) ∈ s ->
  diff_tid_val_at (S tid) d s = (Some tid, v).
Proof.
  intros HNoDup Hin.
  rewrite -elem_of_elements in Hin.
  unfold diff_tid_val_at.
  remember (elements s) as l.
  clear Heql s.
  induction l as [| x l IHl]; first set_solver.
  simpl.
  rewrite fmap_cons NoDup_cons in HNoDup.
  destruct HNoDup as [Hnotin HNoDup].
  rewrite elem_of_cons in Hin.
  destruct Hin.
  - unfold find_tid_val_step.
    rewrite (surjective_pairing x) in H. inversion H.
    destruct (find_tid_val _ _ _).1 eqn:E.
    + pose proof (find_tid_val_spec (S x.1) d l) as Hspec.
      simpl in Hspec. rewrite E in Hspec.
      destruct Hspec as [(Helem & Hlt & _) _].
      assert (Hneq : tid ≠ n).
      { intros Heq. rewrite Heq in H1. set_solver. }
      assert (Hlt' : n < tid) by lia.
      case_decide; [done | lia].
    + case_decide; [done | lia].
  - rewrite IHl; [| auto | auto].
    unfold find_tid_val_step. simpl.
    case_decide; [lia | done].
Qed.

Lemma diff_val_at_S (tid : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  (tid, v) ∈ s ->
  diff_val_at (S tid) d s = v.
Proof.
  intros HNoDup Hin. unfold diff_val_at.
  rewrite (diff_tid_val_at_S _ v); done.
Qed.

Lemma diff_val_at_gt_min_sub_min (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  le_tids_mods tid' s ->
  (tid', v) ∈ s ->
  (tid' < tid)%nat ->
  diff_val_at tid d s = diff_val_at tid v (s ∖ {[(tid', v)]}).
Proof.
  intros HNoDup Hmin Helem Hlt.
  unfold diff_val_at.
  apply union_difference_singleton_L in Helem.
  rewrite {1} Helem.
  set s' := (s ∖ _).
  unfold diff_tid_val_at.
  rewrite (find_tid_val_perm _ _ _ ((tid', v) :: elements s')); last first.
  { apply elements_union_singleton. set_solver. }
  { subst s'. rewrite -union_difference_singleton_L; set_solver. }
  destruct (decide (set_Forall (λ x, tid ≤ x.1)%nat s')).
  - (* No proper TID in the new set [s']. *)
    rewrite -diff_tid_val_at_unfold.
    rewrite (diff_tid_val_at_le_all _ v); last auto.
    simpl.
    rewrite -diff_tid_val_at_unfold diff_tid_val_at_le_all; last done.
    unfold find_tid_val_step. simpl.
    case_decide; [done | lia].
  - apply not_set_Forall_Exists in n; last apply _.
    destruct n as (x & Helem' & Hgt).
    simpl in Hgt. apply not_le in Hgt.
    simpl.
    assert (HExists : Exists (λ x, x.1 < tid)%nat (elements s')).
    { rewrite Exists_exists. exists x. set_solver. }
    rewrite (find_tid_val_Exists _ d v); last auto.
    destruct (find_tid_val_Some tid v (elements s')) as (tidu & u & Heq & _ & Helemu); first auto.
    rewrite Heq.
    unfold find_tid_val_step.
    simpl.
    case_decide; last done.
    assert (contra : (tid' ≤ (tidu, u).1)%nat).
    { unfold set_Forall in Hmin. apply Hmin. set_solver. }
    simpl in contra. lia.
Qed.


Lemma diff_val_at_empty (tid : nat) (v : dbval) :
  diff_val_at tid v ∅ = v.
Proof. done. Qed.

Lemma diff_val_at_extensible (tid tid' : nat) (v : dbval) (s : gset (nat * dbval)) :
  gt_tids_mods tid' s ->
  (tid' ≤ tid)%nat ->
  diff_val_at tid' v s = diff_val_at tid v s.
Proof.
  intros Hallgt Hle.
  unfold diff_val_at, diff_tid_val_at.
  unfold gt_tids_mods in Hallgt.
  rewrite set_Forall_elements in Hallgt.
  rewrite (find_tid_val_extensible tid tid'); auto.
Qed.

Lemma diff_tid_val_at_add_max_le_max (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  gt_tids_mods tid' s ->
  (tid ≤ tid')%nat ->
  diff_tid_val_at tid d ({[(tid', v)]} ∪ s) = diff_tid_val_at tid d s.
Proof.
  intros HNoDup Hgt_all Hle.
  unfold diff_tid_val_at.
  erewrite find_tid_val_perm; last first.
  { apply elements_union_singleton.
    intros contra.
    unfold gt_tids_mods in Hgt_all.
    apply Hgt_all in contra.
    simpl in contra. lia.
  }
  { apply NoDup_elements_fmap_fst_union; last done.
    intros contra.
    apply gt_tids_mods_Forall_fmap_fst in Hgt_all.
    rewrite Forall_forall in Hgt_all.
    apply Hgt_all in contra. lia.
  }
  simpl.
  rewrite find_tid_val_step_noop; [done | by simpl].
Qed.

Lemma diff_val_at_add_max_le_max (tid tid' : nat) (v d : dbval) (s : gset (nat * dbval)) :
  NoDup (elements s).*1 ->
  gt_tids_mods tid' s ->
  (tid ≤ tid')%nat ->
  diff_val_at tid d ({[(tid', v)]} ∪ s) = diff_val_at tid d s.
Proof.
  intros HNoDup Hgt_all Hle.
  unfold diff_val_at.
  rewrite diff_tid_val_at_add_max_le_max; auto.
Qed.

Definition extend {X : Type} (n : nat) (l : list X) :=
  match last l with
  | None => []
  | Some v => l ++ replicate (n - length l) v
  end.

Lemma extend_last {X : Type} (n : nat) (l : list X) :
  last (extend n l) = last l.
Proof.
  unfold extend.
  destruct (last l) eqn:Elast; last done.
  rewrite last_app.
  destruct (last (replicate _ _)) eqn:Erep; last auto.
  apply last_Some_elem_of in Erep.
  apply elem_of_replicate_inv in Erep.
  by f_equal.
Qed.

Lemma extend_length {X : Type} (n : nat) (l : list X) :
  (∃ x, last l = Some x) ->
  length (extend n l) = (n - length l + length l)%nat.
Proof.
  intros [x Hlast].
  unfold extend.
  rewrite Hlast app_length replicate_length.
  lia.
Qed.

Lemma extend_length_ge {X : Type} (n : nat) (l : list X) :
  (length l ≤ length (extend n l))%nat.
Proof.
  unfold extend.
  destruct (last l) eqn:E.
  - rewrite app_length. lia.
  - apply last_None in E. by rewrite E.
Qed.

Lemma extend_length_ge_n {X : Type} (n : nat) (l : list X) :
  (∃ x, last l = Some x) ->
  (n ≤ length (extend n l))%nat.
Proof.
  intros [x Hlast].
  unfold extend.
  rewrite Hlast.
  rewrite app_length.
  rewrite replicate_length.
  lia.
Qed.

Lemma extend_length_same {X : Type} (n : nat) (l : list X) :
  (n ≤ length l)%nat ->
  extend n l = l.
Proof.
  intros Hlen.
  unfold extend.
  destruct (last l) eqn:E.
  - replace (n - length l)%nat with 0%nat by lia. simpl. apply app_nil_r.
  - symmetry. by apply last_None.
Qed.

Lemma extend_last_Some {X : Type} (n : nat) (l : list X) (x : X) :
  last l = Some x ->
  extend n l = l ++ replicate (n - length l) x.
Proof. intros Hlast. unfold extend. by rewrite Hlast. Qed.

Lemma extend_prefix {X : Type} (n : nat) (l : list X) :
  prefix l (extend n l).
Proof.
  unfold extend.
  destruct (last l) eqn:E.
  - unfold prefix. eauto.
  - rewrite last_None in E. by rewrite E.
Qed.

Definition tuple_mods_rel (phys logi : list dbval) (mods : gset (nat * dbval)) :=
  ∃ (diff : list dbval) (v : dbval),
    logi = phys ++ diff ∧
    last phys = Some v ∧
    NoDup (elements mods).*1 ∧
    set_Forall (λ x, (length phys ≤ S x.1 < length logi)%nat) mods ∧
    ∀ (i : nat) (u : dbval), diff !! i = Some u ->
                           u = diff_val_at (i + length phys) v mods.

Lemma tuple_mods_rel_eq_empty (phys logi : list dbval) (mods : gset (nat * dbval)) :
  phys = logi ->
  tuple_mods_rel phys logi mods ->
  mods = ∅.
Proof.
  intros Heq (diff & v & _ & _ & _ & Hlen & _).
  destruct (decide (mods = ∅)); first done.
  apply set_choose_L in n.
  destruct n as [x Helem].
  rewrite Heq in Hlen.
  apply Hlen in Helem. lia.
Qed.

Lemma tuple_mods_rel_last_phys (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  ∃ v, last phys = Some v.
Proof.
  intros Hrel.
  destruct Hrel as (diff & v & _ & H & _).
  by eauto.
Qed.

Lemma tuple_mods_rel_last_logi (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  ∃ v, last logi = Some v.
Proof.
  intros Hrel.
  destruct Hrel as (diff & v & Hprefix & Hphys & _).
  rewrite Hprefix.
  rewrite last_app.
  destruct (last diff); eauto.
Qed.

Lemma tuple_mods_rel_prefix (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  prefix phys logi.
Proof.
  intros Hrel.
  unfold tuple_mods_rel in Hrel.
  destruct Hrel as (diff & v & H & _). unfold prefix.
  by eauto.
Qed.

Theorem tuplext_read (tid : nat) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  (tid < length logi)%nat ->
  le_tids_mods tid mods ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel (extend (S tid) phys) logi mods.
Proof.
  intros Hub Hle_all (diff & v & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  set lenext := (S tid - length phys)%nat.
  exists (drop lenext diff), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast as Heq.
    rewrite Heq Hprefix -app_assoc.
    rewrite app_inv_head_iff.
    rewrite -{1} (take_drop lenext diff).
    rewrite app_inv_tail_iff.
    symmetry. apply replicate_as_Forall.
    split.
    { rewrite take_length_le; first done.
      rewrite Hprefix app_length in Hub. lia.
    }
    rewrite Forall_forall.
    intros u Helem.
    apply elem_of_list_lookup in Helem.
    destruct Helem as [i Hlookup].
    rewrite lookup_take_Some in Hlookup.
    destruct Hlookup as [Hlookup Hle].
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    symmetry. apply diff_val_at_le_all.
    subst lenext.
    assert (H : (i + length phys ≤ tid)%nat) by lia.
    apply le_tids_mods_weaken with tid; auto.
  }
  split.
  { (* last *) rewrite -Hlast. apply extend_last. }
  split; first done.
  split.
  { (* len *)
    unfold le_tids_mods in Hle_all.
    rewrite extend_length; last eauto.
    intros x Helem.
    apply Hlen in Helem as H1.
    apply Hle_all in Helem as H2.
    split; lia.
  }
  { (* diff *)
    intros i u Hlookup.
    rewrite lookup_drop in Hlookup.
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    f_equal.
    rewrite extend_length; [lia | eauto].
  }
Qed.

Theorem tuplext_write (tid : nat) (v : dbval) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  le_tids_mods tid mods ->
  (tid, v) ∈ mods ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel ((extend (S tid) phys) ++ [v]) logi (mods ∖ {[(tid, v)]}).
Proof.
  intros Hle_all Hinmods (diff & w & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  assert (Hub : (S tid < length logi)%nat).
  { apply Hlen in Hinmods. simpl in Hinmods. lia. }
  assert (Hlb : (length phys ≤ S tid)%nat).
  { apply Hlen in Hinmods. simpl in Hinmods. lia. }
  unfold tuple_mods_rel.
  set lenext := S (S tid - length phys)%nat.
  exists (drop lenext diff), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast as Heq.
    rewrite Heq Hprefix -app_assoc -app_assoc.
    rewrite app_inv_head_iff.
    rewrite -{1} (take_drop lenext diff).
    rewrite app_assoc.
    rewrite app_inv_tail_iff.
    rewrite (take_S_r _ _ v); last first.
    { (* value at [tid + 1] *)
      assert (Hgoal : ∃ v', diff !! (S tid - length phys)%nat = Some v').
      { apply list_lookup_lt.
        rewrite Hprefix app_length in Hub. lia.
      }
      destruct Hgoal as [v' Hgoal].
      apply Hdiff in Hgoal as Hv'.
      replace (S tid - _ + _)%nat with (S tid)%nat in Hv' by lia.
      rewrite (diff_val_at_S tid v w mods) in Hv'; [| auto | auto].
      by rewrite Hv' in Hgoal.
    }
    rewrite app_inv_tail_iff.
    symmetry. apply replicate_as_Forall.
    split.
    { rewrite take_length_le; first done.
      rewrite Hprefix app_length in Hub. lia.
    }
    rewrite Forall_forall.
    intros u Helem.
    apply elem_of_list_lookup in Helem.
    destruct Helem as [i Hlookup].
    rewrite lookup_take_Some in Hlookup.
    destruct Hlookup as [Hlookup Hle].
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    symmetry. apply diff_val_at_le_all.
    subst lenext.
    assert (H : (i + length phys ≤ tid)%nat) by lia.
    apply le_tids_mods_weaken with tid; auto.
  }
  split.
  { (* last *) by rewrite last_snoc. }
  split.
  { (* unique *) by apply NoDup_elements_fmap_fst_difference. }
  split.
  { (* len *)
    unfold le_tids_mods in Hle_all.
    rewrite app_length.
    rewrite extend_length; last eauto.
    intros x Helem.
    assert (Helem' : x ∈ mods) by set_solver.
    apply Hlen in Helem' as H1.
    apply Hle_all in Helem' as H2.
    assert (Hneq : x.1 ≠ tid).
    { intros Heq.
      rewrite elem_of_difference in Helem.
      destruct Helem as [_ Hnotin].
      rewrite not_elem_of_singleton in Hnotin.
      replace x with (x.1, x.2) in Helem', Hnotin; last first.
      { symmetry. apply surjective_pairing. }
      subst tid.
      rewrite -elem_of_elements in Hinmods.
      rewrite -elem_of_elements in Helem'.
      assert (Heq : v = x.2).
      { eapply NoDup_perm_fmap_fst; eauto. }
      by subst v.
    }
    simpl.
    split; lia.
  }
  { (* diff *)
    intros i u Hlookup.
    rewrite lookup_drop in Hlookup.
    apply Hdiff in Hlookup.
    rewrite Hlookup.
    rewrite app_length.
    rewrite extend_length; last eauto.
    rewrite (Nat.add_comm _ i).
    rewrite -(Nat.add_assoc i).
    simpl.
    replace (S tid - _ + _)%nat with (S tid)%nat; last lia.
    replace (tid + 1)% nat with (S tid)%nat; last lia.
    replace (S tid + 1)%nat with (S (S tid))%nat; last lia.
    apply diff_val_at_gt_min_sub_min; [auto | auto | auto | lia].
  }
Qed.

Theorem tuplext_linearize_unchanged (tid : nat) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel phys (extend (S tid) logi) mods.
Proof.
  intros Hrel.
  pose proof Hrel as (diff & v & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  assert (Hlast' : ∃ v', last logi = Some v').
  { rewrite Hprefix last_app. destruct (last diff); eauto. }
  destruct Hlast' as [v' Hlast'].
  exists (diff ++ replicate (S tid - length logi) v'), v.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast' as Heq.
    by rewrite Heq Hprefix -app_assoc.
  }
  split.
  { (* last *) done. }
  split; first done.
  split.
  { (* len *)
    apply (set_Forall_impl _ _ _ Hlen).
    intros x Hlt.
    split; first lia.
    apply Nat.lt_le_trans with (length logi); [lia | apply extend_length_ge].
  }
  { (* diff *)
    intros i u Hlookup.
    destruct (decide (i < length diff)%nat).
    - apply Hdiff. by rewrite lookup_app_l in Hlookup; last auto.
    - apply not_lt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_replicate in Hlookup.
      destruct Hlookup as [Heq Hlt]. subst v'.
      (* Case [diff = nil] is treated as a special case. *)
      destruct (decide (diff = [])).
      { rewrite e app_nil_r in Hprefix.
        rewrite (tuple_mods_rel_eq_empty phys logi mods); [| auto | done].
        rewrite diff_val_at_empty. subst logi.
        rewrite Hlast' in Hlast.
        by inversion Hlast.
      }
      (* Use the last value of [logi] as the reference to apply [diff_val_at_extensible]. *)
      rewrite last_lookup in Hlast'.
      rewrite -(diff_val_at_extensible _ (pred (length diff) + length phys)); last first.
      { lia. }
      { unfold gt_tids_mods.
        apply (set_Forall_impl _ _ _ Hlen).
        intros x [_ H].
        rewrite Hprefix app_length in H. lia.
      }
      apply Hdiff.
      rewrite -Hlast'.
      do 2 rewrite -last_lookup.
      rewrite Hprefix.
      rewrite last_app.
      destruct (last diff) eqn:E; [done | by rewrite last_None in E].
  }
Qed.

Theorem tuplext_linearize_changed (tid : nat) (v : dbval) (phys logi : list dbval) (mods : gset (nat * dbval)) :
  (length logi ≤ S tid)%nat ->
  tuple_mods_rel phys logi mods ->
  tuple_mods_rel phys ((extend (S tid) logi) ++ [v]) ({[(tid, v)]} ∪ mods).
Proof.
  intros Hlb Hrel.
  pose proof Hrel as (diff & w & Hprefix & Hlast & HNoDup & Hlen & Hdiff).
  unfold tuple_mods_rel.
  assert (Hlast' : ∃ v', last logi = Some v').
  { rewrite Hprefix last_app. destruct (last diff); eauto. }
  destruct Hlast' as [v' Hlast'].
  exists (diff ++ replicate (S tid - length logi) v' ++ [v]), w.
  split.
  { (* prefix *)
    apply (extend_last_Some (S tid)) in Hlast' as Heq.
    rewrite Heq Hprefix.
    by do 2 rewrite -app_assoc.
  }
  split.
  { (* last *) done. }
  split.
  { apply NoDup_elements_fmap_fst_union; last done.
    intros contra.
    (* Q: ugly... better way? *)
    replace (λ x, (_ ≤ S x.1 < _)%nat) with ((λ n, (length phys ≤ S n < length logi)%nat) ∘ (fst : nat * dbval -> nat)) in Hlen by done.
    rewrite set_Forall_elements -Forall_fmap Forall_forall in Hlen.
    apply Hlen in contra. lia.
  }
  split.
  { (* len *)
    apply set_Forall_union.
    { rewrite set_Forall_singleton. simpl.
      split.
      - trans (length logi); last lia.
        rewrite Hprefix app_length. lia.
      - rewrite app_length. simpl.
        apply Nat.le_lt_trans with (length (extend (S tid) logi)); last lia.
        apply extend_length_ge_n. eauto.
    }
    apply (set_Forall_impl _ _ _ Hlen).
    intros x [H1 H2].
    split; first lia.
    rewrite app_length. simpl.
    apply Nat.lt_le_trans with (length logi); first lia.
    apply Nat.le_trans with (length (extend (S tid) logi)); [apply extend_length_ge | lia].
  }
  { (* diff *)
    intros i u Hlookup.
    assert (Hgt_all : gt_tids_mods tid mods).
    { intros x Helem.
      assert (Hgoal : (S x.1 < S tid)%nat).
      { apply Hlen in Helem. apply Nat.lt_le_trans with (length logi); lia. }
      lia.
    }
    pose proof Hlb as Hlb'.
    rewrite Hprefix app_length in Hlb'.
    destruct (decide (i < S tid - length phys)%nat); last first.
    { apply Nat.nle_gt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_app_r in Hlookup; last first.
      { rewrite replicate_length Hprefix app_length. lia. }
      rewrite list_lookup_singleton_Some in Hlookup.
      destruct Hlookup as [Hi Heq].
      rewrite replicate_length in Hi.
      rewrite Hprefix app_length in Hi.
      assert (Hi' : (i + length phys = S tid)%nat) by lia.
      rewrite Hi'.
      rewrite (diff_val_at_S _ v); [done | | set_solver].
      apply NoDup_elements_fmap_fst_union; last done.
      intros contra.
      apply gt_tids_mods_Forall_fmap_fst in Hgt_all.
      rewrite Forall_forall in Hgt_all.
      apply Hgt_all in contra. lia.
    }
    rewrite diff_val_at_add_max_le_max; [| done | done | lia].
    rewrite app_assoc in Hlookup.
    rewrite lookup_app_l in Hlookup; last first.
    { rewrite app_length replicate_length Hprefix app_length. lia. }
    destruct (decide (i < length diff)%nat).
    - apply Hdiff. by rewrite lookup_app_l in Hlookup; last auto.
    - apply not_lt in n.
      rewrite lookup_app_r in Hlookup; last lia.
      rewrite lookup_replicate in Hlookup.
      destruct Hlookup as [Heq Hlt]. subst v'.
      (* Case [diff = nil] is treated as a special case. *)
      destruct (decide (diff = [])).
      { rewrite e app_nil_r in Hprefix.
        rewrite (tuple_mods_rel_eq_empty phys logi mods); [| auto | done].
        rewrite diff_val_at_empty. subst logi.
        rewrite Hlast' in Hlast.
        by inversion Hlast.
      }
      (* Use the last value of [logi] as the reference to apply [diff_val_at_extensible]. *)
      rewrite last_lookup in Hlast'.
      rewrite -(diff_val_at_extensible _ (pred (length diff) + length phys)); last first.
      { lia. }
      { unfold gt_tids_mods.
        apply (set_Forall_impl _ _ _ Hlen).
        intros x [_ H].
        rewrite Hprefix app_length in H. lia.
      }
      apply Hdiff.
      rewrite -Hlast'.
      do 2 rewrite -last_lookup.
      rewrite Hprefix.
      rewrite last_app.
      destruct (last diff) eqn:E; [done | by rewrite last_None in E].
  }
Qed.

End tuplext.
