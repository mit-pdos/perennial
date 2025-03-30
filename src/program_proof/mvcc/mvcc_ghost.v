From iris.algebra Require Import mono_nat mono_list gmap_view gset.
From Perennial.base_logic Require Import ghost_map mono_nat saved_prop.
From Perennial.program_proof.mvcc Require Import mvcc_prelude.

(* RA definitions. *)
Local Definition vchainR := mono_listR dbvalO.
Local Definition key_vchainR := gmapR u64 vchainR.
Local Definition tidsR := gmap_viewR nat unitR.
Local Definition sid_tidsR := gmapR u64 tidsR.
Local Definition sid_min_tidR := gmapR u64 mono_natR.
Local Definition sid_ownR := gmapR u64 (exclR unitO).

Lemma sids_all_lookup (sid : u64) :
  uint.Z sid < N_TXN_SITES ->
  sids_all !! (uint.nat sid) = Some sid.
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
    #[global] mvcc_ptupleG :: inG Σ key_vchainR;
    #[global] mvcc_ltupleG :: inG Σ key_vchainR;
    #[global] mvcc_abort_tids_ncaG :: ghost_mapG Σ nat unit;
    #[global] mvcc_abort_tids_faG :: ghost_mapG Σ nat unit;
    #[global] mvcc_abort_tids_fciG :: ghost_mapG Σ (nat * dbmap) unit;
    #[global] mvcc_abort_tids_fccG :: ghost_mapG Σ (nat * dbmap) unit;
    #[global] mvcc_commit_tidsG :: ghost_mapG Σ (nat * dbmap) unit;
    #[global] mvcc_dbmapG :: ghost_mapG Σ u64 dbval;
    (* GenTID *)
    #[global] mvcc_tsG :: mono_natG Σ;
    #[global] mvcc_sidG :: inG Σ sid_ownR;
    #[global] mvcc_gentid_reservedG :: ghost_mapG Σ u64 gname;
    #[global] mvcc_gentid_predG :: savedPredG Σ val;
    (* GC *)
    #[global] mvcc_sid_tidsG :: inG Σ sid_tidsR;
    #[global] mvcc_sid_min_tidG :: inG Σ sid_min_tidR;
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
     GFunctor sid_ownR;
     ghost_mapΣ u64 gname;
     savedPredΣ val;
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
    mvcc_abort_tids_nca : gname;
    mvcc_abort_tids_fa : gname;
    mvcc_abort_tmods_fci : gname;
    mvcc_abort_tmods_fcc : gname;
    mvcc_cmt_tmods : gname;
    mvcc_dbmap : gname;
    mvcc_sids : gname;
    mvcc_ts : gname;
    mvcc_gentid_reserved : gname;
    mvcc_sid_tids : gname;
    mvcc_sid_min_tid : gname
  }.

(* Per-txn ghost state. *)
Class mvcc_txn_ghostG Σ :=
  {
    #[global] mvcc_txnmapG :: ghost_mapG Σ u64 dbval;
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

(* TODO: Make it [k q phys]. *)
Definition ptuple_auth_def γ q (k : u64) (phys : list dbval) : iProp Σ :=
  own γ (A:=key_vchainR) {[k := ●ML{# q } phys]}.

Definition ptuple_auth γ q (k : u64) (phys : list dbval) : iProp Σ :=
  ptuple_auth_def γ.(mvcc_ptuple) q k phys.

Definition ptuple_lb γ (k : u64) (phys : list dbval) : iProp Σ :=
  own γ.(mvcc_ptuple) {[k := ◯ML phys]}.

Definition ltuple_auth_def γ (k : u64) (logi : list dbval) : iProp Σ :=
  own γ {[k := ●ML logi]}.

Definition ltuple_auth γ (k : u64) (logi : list dbval) : iProp Σ :=
  ltuple_auth_def γ.(mvcc_ltuple) k logi.

Definition ltuple_lb γ (k : u64) (logi : list dbval) : iProp Σ :=
  own γ.(mvcc_ltuple) {[k := ◯ML logi]}.

Definition ptuple_ptsto γ (k : u64) (v : dbval) (ts : nat) : iProp Σ :=
  ∃ phys, ptuple_lb γ k phys ∗ ⌜phys !! ts = Some v⌝.

Definition mods_token γ (k : u64) (ts : nat) : iProp Σ :=
  ∃ phys, ptuple_auth γ (1/4) k phys ∗ ⌜(length phys ≤ S ts)%nat⌝.

Definition ltuple_ptsto γ (k : u64) (v : dbval) (ts : nat) : iProp Σ :=
  ∃ logi, ltuple_lb γ k logi ∗ ⌜logi !! ts = Some v⌝.

Definition ltuple_ptstos γ (m : dbmap) (ts : nat) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, ltuple_ptsto γ k v ts.

(* Definitions about GC-related resources. *)
Definition site_active_tids_auth_def γ (sid : u64) q (tids : gset nat) : iProp Σ :=
  own γ {[sid := (gmap_view_auth (DfracOwn q) (gset_to_gmap tt tids))]}.

Definition site_active_tids_auth γ sid tids : iProp Σ :=
  site_active_tids_auth_def γ.(mvcc_sid_tids) sid 1 tids.

Definition site_active_tids_half_auth γ sid tids : iProp Σ :=
  site_active_tids_auth_def γ.(mvcc_sid_tids) sid (1 / 2) tids.

Definition site_active_tids_frag_def γ (sid : u64) tid : iProp Σ :=
  own γ {[sid := (gmap_view_frag tid (DfracOwn 1) tt)]}.

Definition site_active_tids_frag γ (sid : u64) tid : iProp Σ :=
  site_active_tids_frag_def γ.(mvcc_sid_tids) sid tid.

(* TODO: should be able to remove the second conjunct. *)
Definition active_tid γ (tid sid : u64) : iProp Σ :=
  (site_active_tids_frag γ sid (uint.nat tid) ∧ ⌜uint.Z sid < N_TXN_SITES⌝) ∧ ⌜(0 < uint.Z tid < 2 ^ 64 - 1)⌝ .

Definition site_min_tid_auth_def γ (sid : u64) q tid : iProp Σ :=
  own γ {[sid := (●MN{# q} tid)]}.

Definition site_min_tid_auth γ (sid : u64) tid : iProp Σ :=
  site_min_tid_auth_def γ.(mvcc_sid_min_tid) sid 1 tid.

Definition site_min_tid_lb γ (sid : u64) tid : iProp Σ :=
  own γ.(mvcc_sid_min_tid) {[sid := (◯MN tid)]}.

Definition min_tid_lb γ tid : iProp Σ :=
  [∗ list] sid ∈ sids_all, site_min_tid_lb γ sid tid.

(* Definitions about SST-related resources. *)
Definition ts_auth γ (ts : nat) : iProp Σ :=
  mono_nat_auth_own γ.(mvcc_ts) (1/2) ts.

Definition ts_lb γ (ts : nat) : iProp Σ :=
  mono_nat_lb_own γ.(mvcc_ts) ts.

Definition sid_own γ (sid : u64) : iProp Σ :=
  own γ.(mvcc_sids) ({[ sid := Excl () ]}).

Definition nca_tids_auth γ (tids : gset nat) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tids_nca) 1 (gset_to_gmap tt tids).

Definition nca_tids_frag γ (tid : nat) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tids_nca) tid (DfracOwn 1) tt.

Definition fa_tids_auth γ (tids : gset nat) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tids_fa) 1 (gset_to_gmap tt tids).

Definition fa_tids_frag γ (tid : nat) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tids_fa) tid (DfracOwn 1) tt.

Definition fci_tmods_auth (γ : mvcc_names) (tmods : gset (nat * dbmap)) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tmods_fci) 1 (gset_to_gmap tt tmods).

Definition fci_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tmods_fci) tmod (DfracOwn 1) tt.

Definition fcc_tmods_auth (γ : mvcc_names) (tmods : gset (nat * dbmap)) : iProp Σ :=
  ghost_map_auth γ.(mvcc_abort_tmods_fcc) 1 (gset_to_gmap tt tmods).

Definition fcc_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_abort_tmods_fcc) tmod (DfracOwn 1) tt.

Definition cmt_tmods_auth (γ : mvcc_names) (tmods : gset (nat * dbmap)) : iProp Σ :=
  ghost_map_auth γ.(mvcc_cmt_tmods) 1 (gset_to_gmap tt tmods).

Definition cmt_tmods_frag γ (tmod : nat * dbmap) : iProp Σ :=
  ghost_map_elem γ.(mvcc_cmt_tmods) tmod (DfracOwn 1) tt.

Definition dbmap_auth γ (m : dbmap) : iProp Σ :=
  ghost_map_auth γ.(mvcc_dbmap) 1 m.

Definition dbmap_ptsto γ k q (v : dbval) : iProp Σ :=
  ghost_map_elem γ.(mvcc_dbmap) k (DfracOwn q) v.

Definition dbmap_ptstos γ q (m : dbmap) : iProp Σ :=
  [∗ map] k ↦ v ∈ m, dbmap_ptsto γ k q v.

(* Definitions about per-txn resources. *)
Definition txnmap_auth τ (m : dbmap) : iProp Σ :=
  ghost_map_auth τ 1 m.

Definition txnmap_ptsto τ k (v : dbval) : iProp Σ :=
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
  iIntros "%Hq Hv". subst q.
  iDestruct "Hv" as "[Hv1 Hv2]".
  iFrame.
Qed.

Lemma vchain_witness γ q k vchain :
  ptuple_auth γ q k vchain -∗ ptuple_lb γ k vchain.
Proof.
  iApply own_mono.
  apply singleton_included_mono, mono_list_included.
Qed.

Lemma ptuple_prefix γ q k l l' :
  ptuple_auth γ q k l -∗
  ptuple_lb γ k l' -∗
  ⌜prefix l' l⌝.
Proof.
  iIntros "Hl Hl'".
  iDestruct (own_valid_2 with "Hl Hl'") as %Hvalid.
  iPureIntro. revert Hvalid.
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
  iIntros "%Hprefix Hv1 Hv2".
  iAssert (ptuple_auth γ 1 key vchain') with "[> Hv1 Hv2]" as "[Hv1 Hv2]".
  { iCombine "Hv1 Hv2" as "Hv".
    iApply (own_update with "Hv").
    apply singleton_update, mono_list_update.
    done.
  }
  by iFrame.
Qed.

Lemma vchain_false {γ q key vchain} :
  (1 < q)%Qp ->
  ptuple_auth γ q key vchain -∗
  False.
Proof.
  iIntros (Hq) "Hv".
  iDestruct (own_valid with "Hv") as %Hvalid.
  rewrite singleton_valid mono_list_auth_dfrac_valid dfrac_valid_own in Hvalid.
  apply Qp.lt_nge in Hq.
  done.
Qed.

Lemma ptuple_agree {γ q1 q2 key vchain1 vchain2} :
  ptuple_auth γ q1 key vchain1 -∗
  ptuple_auth γ q2 key vchain2 -∗
  ⌜vchain1 = vchain2⌝.
Proof.
  iIntros "Hv1 Hv2".
  iDestruct (own_valid_2 with "Hv1 Hv2") as %Hvalid.
  rewrite singleton_op singleton_valid mono_list_auth_dfrac_op_valid_L in Hvalid.
  by destruct Hvalid as [_ Hv].
Qed.

Lemma ltuple_update {γ key l} l' :
  prefix l l' →
  ltuple_auth γ key l ==∗
  ltuple_auth γ key l'.
Proof.
  iIntros "%Hprefix Hl".
  iApply (own_update with "Hl").
  apply singleton_update, mono_list_update.
  done.
Qed.

Lemma ltuple_witness γ k l :
  ltuple_auth γ k l -∗ ltuple_lb γ k l.
Proof.
  iApply own_mono.
  apply singleton_included_mono, mono_list_included.
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
  site_active_tids_half_auth γ sid tids -∗ site_active_tids_frag γ sid tid -∗ ⌜tid ∈ tids⌝.
Proof.
  iIntros "Hauth Helem".
  iDestruct (own_valid_2 with "Hauth Helem") as %Hvalid.
  rewrite singleton_op singleton_valid in Hvalid.
  apply gmap_view_both_dfrac_valid_discrete_total in Hvalid.
  destruct Hvalid as (v' & _ & _ & Hlookup & _ & _).
  apply elem_of_dom_2 in Hlookup.
  rewrite dom_gset_to_gmap in Hlookup.
  done.
Qed.

Lemma site_active_tids_agree γ (sid : u64) tids tids' :
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids' -∗
  ⌜tids = tids'⌝.
Proof.
  iIntros "Hauth1 Hauth2".
  iDestruct (own_valid_2 with "Hauth1 Hauth2") as %Hvalid.
  rewrite singleton_op singleton_valid in Hvalid.
  apply gmap_view_auth_dfrac_op_valid in Hvalid.
  destruct Hvalid as [_ Etids].
  iPureIntro.
  rewrite -(dom_gset_to_gmap tids ()) -(dom_gset_to_gmap tids' ()).
  by rewrite Etids.
Qed.

Lemma site_active_tids_insert {γ sid tids} tid :
  tid ∉ tids ->
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid ({[ tid ]} ∪ tids) ∗
  site_active_tids_half_auth γ sid ({[ tid ]} ∪ tids) ∗
  site_active_tids_frag γ sid tid.
Proof.
  iIntros "%Hdom Hauth1 Hauth2".
  iAssert (site_active_tids_auth γ sid ({[ tid ]} ∪ tids) ∗ site_active_tids_frag γ sid tid)%I
    with "[> Hauth1 Hauth2]" as "[[Hauth1 Hauth2] Hfrag]".
  { iCombine "Hauth1 Hauth2" as "Hauth".
    rewrite -own_op singleton_op.
    iApply (own_update with "Hauth").
    apply singleton_update.
    rewrite gset_to_gmap_union_singleton.
    (* Q: What's the difference between [apply] (which fails here) and [apply:]? *)
    apply: gmap_view_alloc; last done; last done.
    by rewrite lookup_gset_to_gmap_None.
  }
  by iFrame.
Qed.

Lemma site_active_tids_delete {γ sid tids} tid :
  site_active_tids_frag γ sid tid -∗
  site_active_tids_half_auth γ sid tids -∗
  site_active_tids_half_auth γ sid tids ==∗
  site_active_tids_half_auth γ sid (tids ∖ {[ tid ]}) ∗
  site_active_tids_half_auth γ sid (tids ∖ {[ tid ]}).
Proof.
  iIntros "Hfrag Hauth1 Hauth2".
  iAssert (site_active_tids_auth γ sid (tids ∖ {[ tid ]}))%I
    with "[> Hfrag Hauth1 Hauth2]" as "[Hauth1 Hauth2]".
  { iCombine "Hauth1 Hauth2" as "Hauth".
    iApply (own_update_2 with "Hauth Hfrag").
    rewrite singleton_op.
    rewrite gset_to_gmap_difference_singleton.
    apply singleton_update.
    apply: gmap_view_delete.
  }
  by iFrame.
Qed.

Lemma site_min_tid_valid γ (sid : u64) tidN tidlbN :
  site_min_tid_auth γ sid tidN -∗
  site_min_tid_lb γ sid tidlbN -∗
  ⌜(tidlbN ≤ tidN)%nat⌝.
Proof.
  iIntros "Hauth Hlb".
  iDestruct (own_valid_2 with "Hauth Hlb") as %Hvalid.
  rewrite singleton_op singleton_valid mono_nat_both_dfrac_valid in Hvalid.
  by destruct Hvalid as [_ Hle].
Qed.

Lemma site_min_tid_lb_weaken γ (sid : u64) tidN tidN' :
  (tidN' ≤ tidN)%nat ->
  site_min_tid_lb γ sid tidN -∗
  site_min_tid_lb γ sid tidN'.
Proof.
  iIntros "%Hle Hlb".
  iApply (own_mono with "Hlb").
  apply singleton_included_mono.
  apply mono_nat_lb_mono.
  done.
Qed.

Lemma site_min_tid_update {γ sid tid} tid' :
  (tid ≤ tid')%nat ->
  site_min_tid_auth γ sid tid ==∗
  site_min_tid_auth γ sid tid'.
Proof.
  iIntros "%Hle Hauth".
  iApply (own_update with "Hauth").
  apply singleton_update, mono_nat_update.
  done.
Qed.

Lemma site_min_tid_witness {γ sid tid} :
  site_min_tid_auth γ sid tid -∗
  site_min_tid_lb γ sid tid.
Proof.
  iApply own_mono.
  apply singleton_included_mono, mono_nat_included.
Qed.

Lemma min_tid_lb_zero γ :
  ([∗ list] sid ∈ sids_all, ∃ tid, site_min_tid_auth γ sid tid) -∗
  min_tid_lb γ 0%nat.
Proof.
  iApply big_sepL_mono.
  iIntros (sidN sid) "%Hlookup Hauth".
  iDestruct "Hauth" as (tid) "Hauth".
  iDestruct (site_min_tid_witness with "Hauth") as "Hlb".
  iRevert "Hlb".
  iApply site_min_tid_lb_weaken.
  lia.
Qed.

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

Lemma ptuples_alloc :
  ⊢ |==> ∃ γ, ([∗ set] key ∈ keys_all, ptuple_auth_def γ (1 / 2) key [Nil; Nil]) ∗
              ([∗ set] key ∈ keys_all, ptuple_auth_def γ (1 / 2) key [Nil; Nil]).
Proof.
  set m := gset_to_gmap (●ML ([Nil; Nil])) keys_all.
  iMod (own_alloc m) as (γ) "Htpls".
  { intros k.
    rewrite lookup_gset_to_gmap option_guard_True; last apply elem_of_fin_to_set.
    rewrite Some_valid.
    apply mono_list_auth_valid.
  }
  iModIntro. iExists γ.
  iAssert ([∗ set] key ∈ keys_all, ptuple_auth_def γ 1 key [Nil; Nil])%I
    with "[Htpls]" as "Htpls".
  { rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace keys_all with (dom m); last by by rewrite dom_gset_to_gmap.
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Htpls").
    iIntros "!>" (k v). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ <-]) "Htpls".
    done.
  }
  rewrite -big_sepS_sep.
  iApply (big_sepS_mono with "Htpls").
  iIntros (k Helem) "[Htpl1 Htpl2]".
  iFrame.
Qed.

Lemma ltuples_alloc :
  ⊢ |==> ∃ γ, ([∗ set] key ∈ keys_all, ltuple_auth_def γ key [Nil; Nil]).
Proof.
  set m := gset_to_gmap (●ML ([Nil; Nil])) keys_all.
  iMod (own_alloc m) as (γ) "Htpls".
  { intros k.
    rewrite lookup_gset_to_gmap option_guard_True; last apply elem_of_fin_to_set.
    rewrite Some_valid.
    apply mono_list_auth_valid.
  }
  iModIntro. iExists γ.
  rewrite -(big_opM_singletons m).
  rewrite big_opM_own_1.
  replace keys_all with (dom m); last by by rewrite dom_gset_to_gmap.
  iApply big_sepM_dom.
  iApply (big_sepM_impl with "Htpls").
  iIntros "!>" (k v). subst m.
  rewrite lookup_gset_to_gmap_Some.
  iIntros ([_ <-]) "Htpls".
  done.
Qed.

Lemma site_active_tids_alloc :
  ⊢ |==> ∃ γ, ([∗ list] sid ∈ sids_all, site_active_tids_auth_def γ sid (1 / 2) ∅) ∗
              ([∗ list] sid ∈ sids_all, site_active_tids_auth_def γ sid (1 / 2) ∅).
Proof.
  set u64_all : gset u64 := (fin_to_set u64).
  set m := gset_to_gmap (gmap_view_auth (DfracOwn 1) (∅ : gmap nat unit)) u64_all.
  iMod (own_alloc m) as (γ) "Hown".
  { intros k.
    rewrite lookup_gset_to_gmap option_guard_True; last apply elem_of_fin_to_set.
    rewrite Some_valid.
    apply gmap_view_auth_valid.
  }
  iModIntro. iExists γ.
  iAssert ([∗ set] sid ∈ u64_all, site_active_tids_auth_def γ sid 1 ∅)%I
    with "[Hown]" as "Hown".
  { rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace u64_all with (dom m); last by by rewrite dom_gset_to_gmap.
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!>" (k v). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ <-]) "Hown".
    unfold site_active_tids_auth_def.
    iFrame.
  }
  set sids : gset u64 := list_to_set sids_all.
  iDestruct (big_sepS_subseteq _ _ sids with "Hown") as "Hown"; first set_solver.
  subst sids.
  rewrite big_sepS_list_to_set; last first.
  { unfold sids_all. apply seq_U64_NoDup; word. }
  rewrite -big_sepL_sep.
  iApply (big_sepL_mono with "Hown").
  iIntros (sid sidN Helem) "[H1 H2]".
  iFrame.
Qed.

Lemma site_min_tid_alloc :
  ⊢ |==> ∃ γ, ([∗ list] sid ∈ sids_all, site_min_tid_auth_def γ sid 1 0).
Proof.
  set u64_all : gset u64 := (fin_to_set u64).
  set m := gset_to_gmap (●MN 0) u64_all.
  iMod (own_alloc m) as (γ) "Hown".
  { intros k.
    rewrite lookup_gset_to_gmap option_guard_True; last apply elem_of_fin_to_set.
    rewrite Some_valid.
    apply mono_nat_auth_valid.
  }
  iModIntro. iExists γ.
  iAssert ([∗ set] sid ∈ u64_all, site_min_tid_auth_def γ sid 1 0)%I
    with "[Hown]" as "Hown".
  { rewrite -(big_opM_singletons m).
    rewrite big_opM_own_1.
    replace u64_all with (dom m); last by by rewrite dom_gset_to_gmap.
    iApply big_sepM_dom.
    iApply (big_sepM_impl with "Hown").
    iIntros "!>" (k v). subst m.
    rewrite lookup_gset_to_gmap_Some.
    iIntros ([_ <-]) "Hown".
    done.
  }
  set sids : gset u64 := list_to_set sids_all.
  iDestruct (big_sepS_subseteq _ _ sids with "Hown") as "Hown"; first set_solver.
  subst sids.
  rewrite big_sepS_list_to_set; last first.
  { unfold sids_all. apply seq_U64_NoDup; word. }
  done.
Qed.

Definition mvcc_gentid_init γ : iProp Σ :=
  ts_auth γ 0%nat ∗ ghost_map_auth γ.(mvcc_gentid_reserved) 1 (∅ : gmap u64 gname).

Lemma mvcc_ghost_alloc :
  ⊢ |==> ∃ γ,
    (* SST-related. *)
    ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
    ([∗ set] key ∈ keys_all, ptuple_auth γ (1/2) key [Nil; Nil]) ∗
    ([∗ set] key ∈ keys_all, ltuple_auth γ key [Nil; Nil]) ∗
    ts_auth γ 0%nat ∗
    ([∗ list] sid ∈ sids_all, sid_own γ sid) ∗
    nca_tids_auth γ ∅ ∗
    fa_tids_auth γ ∅ ∗
    fci_tmods_auth γ ∅ ∗
    fcc_tmods_auth γ ∅ ∗
    cmt_tmods_auth γ ∅ ∗
    let dbmap_init := (gset_to_gmap Nil keys_all) in
    dbmap_auth γ dbmap_init ∗
    ([∗ map] k ↦ v ∈ dbmap_init, dbmap_ptsto γ k 1 v) ∗
    mvcc_gentid_init γ ∗
    (* GC-related. *)
    ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
    ([∗ list] sid ∈ sids_all, site_active_tids_half_auth γ sid ∅) ∗
    ([∗ list] sid ∈ sids_all, site_min_tid_auth γ sid 0).
Proof.
  iMod ptuples_alloc as (γptuple) "[Hptpls1 Hptpls2]".
  iMod ltuples_alloc as (γltuple) "Hltpls".
  iMod (mono_nat_own_alloc 0) as (γts) "[[Hts1 Hts2] _]".
  set sids : gset u64 := list_to_set sids_all.
  iMod (own_alloc (A:=sid_ownR) (gset_to_gmap (Excl tt) sids)) as (γsids) "Hsids".
  { intros k. rewrite lookup_gset_to_gmap. destruct (decide (k ∈ sids)).
    - rewrite option_guard_True //.
    - rewrite option_guard_False //. }
  iMod (ghost_map_alloc (∅ : gmap nat unit)) as (γnca) "[Hnca _]".
  iMod (ghost_map_alloc (∅ : gmap nat unit)) as (γfa) "[Hfa _]".
  iMod (ghost_map_alloc (∅ : gmap (nat * dbmap) unit)) as (γfci) "[Hfci _]".
  iMod (ghost_map_alloc (∅ : gmap (nat * dbmap) unit)) as (γfcc) "[Hfcc _]".
  iMod (ghost_map_alloc (∅ : gmap (nat * dbmap) unit)) as (γcmt) "[Hcmt _]".
  iMod (ghost_map_alloc (gset_to_gmap Nil keys_all)) as (γm) "[Hm Hpts]".
  iMod (ghost_map_alloc (∅ : gmap u64 gname)) as (γres) "[Hres _]".
  iMod site_active_tids_alloc as (γactive) "[Hacts1 Hacts2]".
  iMod site_min_tid_alloc as (γmin) "Hmin".
  set γ :=
    {|
      mvcc_ptuple := γptuple;
      mvcc_ltuple := γltuple;
      mvcc_ts := γts;
      mvcc_sids := γsids;
      mvcc_abort_tids_nca := γnca;
      mvcc_abort_tids_fa := γfa;
      mvcc_abort_tmods_fci := γfci;
      mvcc_abort_tmods_fcc := γfcc;
      mvcc_cmt_tmods := γcmt;
      mvcc_dbmap := γm;
      mvcc_gentid_reserved := γres;
      mvcc_sid_tids := γactive;
      mvcc_sid_min_tid := γmin
    |}. 
  iExists γ. rewrite /mvcc_gentid_init.
  iAssert ([∗ list] sid ∈ sids_all, sid_own γ sid)%I with "[Hsids]" as "Hsids".
  { iEval (rewrite -[gset_to_gmap _ _]big_opM_singletons) in "Hsids".
    rewrite big_opM_own_1. rewrite big_opM_map_to_list.
    rewrite map_to_list_gset_to_gmap. subst sids.
    rewrite big_sepL_fmap elements_list_to_set.
    2:{ unfold sids_all. apply NoDup_fmap_2_strong, NoDup_seqZ.
        clear. intros x y Hx%elem_of_seqZ Hy%elem_of_seqZ Heq.
        word.
    }
    iFrame.
  }
  iFrame.
  unfold nca_tids_auth, fa_tids_auth, fci_tmods_auth, fcc_tmods_auth, cmt_tmods_auth.
  by iFrame.
Qed.

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
Proof. apply: ghost_map_lookup. Qed.

Lemma txnmap_lookup_big τ m m' :
  txnmap_auth τ m -∗
  txnmap_ptstos τ m' -∗
  ⌜m' ⊆ m⌝.
Proof. apply: ghost_map_lookup_big. Qed.

Lemma txnmap_update {τ m k v} w :
  txnmap_auth τ m -∗
  txnmap_ptsto τ k v ==∗
  txnmap_auth τ (<[ k := w ]> m) ∗
  txnmap_ptsto τ k w.
Proof. apply: ghost_map_update. Qed.

Lemma txnmap_alloc m :
  ⊢ |==> ∃ τ, txnmap_auth τ m ∗ ([∗ map] k ↦ v ∈ m, txnmap_ptsto τ k v).
Proof. apply: ghost_map_alloc. Qed.

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

Lemma fci_tmods_insert {γ : mvcc_names} {tmods : gset (nat * dbmap)} tmod :
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
