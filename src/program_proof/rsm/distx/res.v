(** Global resources. *)
(* From Perennial.program_proof.rsm.distx Require Import top. *)
From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import vslice.
From Perennial.program_proof.rsm.distx Require Import base.

Section res.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  Definition db_ptsto γ (k : dbkey) (v : dbval) : iProp Σ.
  Admitted.

  Definition db_ptstos γ (m : dbmap) : iProp Σ :=
    [∗ map] k ↦ v ∈ m, db_ptsto γ k v.

  Definition hist_repl_half γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  Definition hist_repl_lb γ (k : dbkey) (h : dbhist) : iProp Σ.
  Admitted.

  #[global]
  Instance is_hist_repl_lb_persistent α key hist :
    Persistent (hist_repl_lb α key hist).
  Admitted.

  Lemma hist_repl_witness {γ k h} :
    hist_repl_half γ k h -∗
    hist_repl_lb γ k h.
  Admitted.

  Definition hist_repl_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ :=
    ∃ hist, ⌜hist !! ts = Some v⌝ ∗ hist_repl_lb γ k hist.

  Definition hist_lnrz_half γ (k : dbkey) (l : dbhist) : iProp Σ.
  Admitted.

  Definition hist_lnrz_at γ (k : dbkey) (ts : nat) (v : dbval) : iProp Σ.
  Admitted.

  Definition ts_repl_half γ (k : dbkey) (ts : nat) : iProp Σ.
  Admitted.

  Definition tuple_repl_half γ (k : dbkey) (t : dbtpl) : iProp Σ :=
    hist_repl_half γ k t.1 ∗ ts_repl_half γ k t.2.

  Lemma tuple_repl_agree {γ k t1 t2} :
    tuple_repl_half γ k t1 -∗
    tuple_repl_half γ k t2 -∗
    ⌜t2 = t1⌝.
  Admitted.

  Lemma tuple_repl_big_agree {γ tpls1 tpls2} :
    dom tpls1 = dom tpls2 ->
    ([∗ map] k ↦ t ∈ tpls1, tuple_repl_half γ k t) -∗
    ([∗ map] k ↦ t ∈ tpls2, tuple_repl_half γ k t) -∗
    ⌜tpls2 = tpls1⌝.
  Admitted.
  
  Lemma tuple_repl_update {γ k t1 t2} t' :
    tuple_repl_half γ k t1 -∗
    tuple_repl_half γ k t2 ==∗
    tuple_repl_half γ k t' ∗ tuple_repl_half γ k t'.
  Admitted.

  Lemma tuple_repl_big_update {γ tpls} tpls' :
    dom tpls = dom tpls' ->
    ([∗ map] k ↦ t ∈ tpls, tuple_repl_half γ k t) -∗
    ([∗ map] k ↦ t ∈ tpls, tuple_repl_half γ k t) ==∗
    ([∗ map] k ↦ t ∈ tpls', tuple_repl_half γ k t) ∗
    ([∗ map] k ↦ t ∈ tpls', tuple_repl_half γ k t).
  Admitted.

  (* Transaction result map RA. *)
  Definition txnres_auth γ (resm : gmap nat txnres) : iProp Σ.
  Admitted.

  Definition txnres_receipt γ (ts : nat) (res : txnres) : iProp Σ.
  Admitted.

  #[global]
  Instance txnres_receipt_persistent γ ts res :
    Persistent (txnres_receipt γ ts res).
  Admitted.

  Definition txnres_cmt γ ts wrs :=
    txnres_receipt γ ts (ResCommitted wrs).

  Definition txnres_abt γ ts :=
    txnres_receipt γ ts ResAborted.

  Lemma txnres_insert {γ resm} ts res :
    resm !! ts = None ->
    txnres_auth γ resm ==∗
    txnres_auth γ (<[ts := res]> resm).
  Admitted.

  Lemma txnres_witness γ resm ts res :
    resm !! ts = Some res ->
    txnres_auth γ resm -∗
    txnres_receipt γ ts res.
  Admitted.

  Lemma txnres_lookup γ resm ts res :
    txnres_auth γ resm -∗
    txnres_receipt γ ts res -∗
    ⌜resm !! ts = Some res⌝.
  Admitted.

  (* Transaction write-sets. This resource allows us to specify that [CmdPrep]
  is submitted to only the participant group, as encoded in
  [safe_submit]. Without which we won't be able to prove that learning a commit
  under an aborted state is impossible, as a non-participant group could have
  received [CmdPrep] and aborted. *)
  Definition txnwrs_auth γ (wrsm : gmap nat dbmap) : iProp Σ.
  Admitted.

  Definition txnwrs_receipt γ (ts : nat) (wrs : dbmap) : iProp Σ.
  Admitted.

  #[global]
  Instance txnwrs_receipt_persistent γ ts wrs  :
    Persistent (txnwrs_receipt γ ts wrs).
  Admitted.

  Lemma txnwrs_receipt_agree γ ts wrs1 wrs2 :
    txnwrs_receipt γ ts wrs1 -∗
    txnwrs_receipt γ ts wrs2 -∗
    ⌜wrs2 = wrs1⌝.
  Admitted.

  Lemma txnwrs_lookup γ wrsm ts wrs :
    txnwrs_auth γ wrsm -∗
    txnwrs_receipt γ ts wrs -∗
    ⌜wrsm !! ts = Some wrs⌝.
  Admitted.

  (* Custom transaction status. *)
  Definition txnprep_auth γ (gid : groupid) (pm : gmap nat bool) : iProp Σ.
  Admitted.

  Definition txnprep_receipt γ (gid : groupid) (ts : nat) (p : bool) : iProp Σ.
  Admitted.

  #[global]
  Instance txnprep_receipt_persistent γ gid ts p :
    Persistent (txnprep_receipt γ gid ts p).
  Admitted.

  Definition txnprep_prep γ gid ts :=
    txnprep_receipt γ gid ts true.

  Definition txnprep_unprep γ gid ts :=
    txnprep_receipt γ gid ts false.

  Lemma txnprep_receipt_agree γ gid ts p1 p2 :
    txnprep_receipt γ gid ts p1 -∗
    txnprep_receipt γ gid ts p2 -∗
    ⌜p2 = p1⌝.
  Admitted.

  Lemma txnprep_insert {γ gid pm} ts p :
    pm !! ts = None ->
    txnprep_auth γ gid pm ==∗
    txnprep_auth γ gid (<[ts := p]> pm).
  Admitted.

  Lemma txnprep_witness γ gid pm ts p :
    pm !! ts = Some p ->
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p.
  Admitted.

  Lemma txnprep_lookup γ gid pm ts p :
    txnprep_auth γ gid pm -∗
    txnprep_receipt γ gid ts p -∗
    ⌜pm !! ts = Some p⌝.
  Admitted.

  Definition kmod_lnrz_half γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Lemma kmod_lnrz_agree {γ k m1 m2} :
    kmod_lnrz_half γ k m1 -∗
    kmod_lnrz_half γ k m2 -∗
    ⌜m2 = m1⌝.
  Admitted.

  Lemma kmod_lnrz_vslice_agree {γ k m im} :
    k ∈ keys_all ->
    ([∗ set] key ∈ keys_all, kmod_lnrz_half γ key (vslice m key)) -∗
    kmod_lnrz_half γ k im -∗
    ⌜im = vslice m k⌝.
  Proof.
    iIntros (Hin) "Hkeys Hk".
    iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hin.
    by iDestruct (kmod_lnrz_agree with "Hkey Hk") as %?.
  Qed.

  Definition kmod_cmtd_half γ (k : dbkey) (kmod : dbkmod) : iProp Σ.
  Admitted.

  Lemma kmod_cmtd_agree {γ k m1 m2} :
    kmod_cmtd_half γ k m1 -∗
    kmod_cmtd_half γ k m2 -∗
    ⌜m2 = m1⌝.
  Admitted.

  Lemma kmod_cmtd_vslice_agree {γ k m im} :
    k ∈ keys_all ->
    ([∗ set] key ∈ keys_all, kmod_cmtd_half γ key (vslice m key)) -∗
    kmod_cmtd_half γ k im -∗
    ⌜im = vslice m k⌝.
  Proof.
    iIntros (Hin) "Hkeys Hk".
    iDestruct (big_sepS_elem_of with "Hkeys") as "Hkey"; first apply Hin.
    by iDestruct (kmod_cmtd_agree with "Hkey Hk") as %?.
  Qed.

  (* Linearized transactions. *)
  Definition txns_lnrz_auth γ (tids : gset nat) : iProp Σ.
  Admitted.

  Definition txns_lnrz_receipt γ (tid : nat) : iProp Σ.
  Admitted.

  #[global]
  Instance txns_lnrz_receipt_persistent γ tid :
    Persistent (txns_lnrz_receipt γ tid).
  Admitted.

  Lemma txns_lnrz_union γ tids tid :
    tid ∉ tids ->
    txns_lnrz_auth γ tids ==∗
    txns_lnrz_auth γ ({[ tid ]} ∪ tids) ∗ txns_lnrz_receipt γ tid.
  Admitted.

  Lemma txns_lnrz_witness γ tids tid :
    tid ∈ tids ->
    txns_lnrz_auth γ tids -∗
    txns_lnrz_receipt γ tid.
  Admitted.

  Lemma txns_lnrz_elem_of γ tids tid :
    txns_lnrz_auth γ tids -∗
    txns_lnrz_receipt γ tid -∗
    ⌜tid ∈ tids⌝.
  Admitted.

  (* Paxos log and command pool. TODO: rename clog to just log. *)
  Definition clog_half γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  Definition clog_lb γ (gid : groupid) (log : dblog) : iProp Σ.
  Admitted.

  #[global]
  Instance clog_lb_persistent γ gid log :
    Persistent (clog_lb γ gid log).
  Admitted.

  Definition clog_lbs γ (logs : gmap groupid dblog) : iProp Σ :=
    [∗ map] gid ↦ log ∈ logs, clog_lb γ gid log.

  Definition cpool_half γ (gid : groupid) (cpool : gset command) : iProp Σ.
  Admitted.

  Definition cmd_receipt γ (gid : groupid) (lsn : nat) (term : nat) (c : command) : iProp Σ.
  Admitted.

  #[global]
  Instance cmd_receipt_persistent γ gid lsn term c :
    Persistent (cmd_receipt γ gid lsn term c).
  Admitted.

  Lemma log_witness γ gid log :
    clog_half γ gid log -∗
    clog_lb γ gid log.
  Admitted.

  Lemma log_prefix γ gid log logp :
    clog_half γ gid log -∗
    clog_lb γ gid logp -∗
    ⌜prefix logp log⌝.
  Admitted.

  Lemma log_lb_prefix γ gid logp1 logp2 :
    clog_lb γ gid logp1 -∗
    clog_lb γ gid logp2 -∗
    ⌜prefix logp1 logp2 ∨ prefix logp2 logp1⌝.
  Admitted.

  Lemma log_lb_weaken {γ gid} logp1 logp2 :
    prefix logp1 logp2 ->
    clog_lb γ gid logp2 -∗
    clog_lb γ gid logp1.
  Admitted.

  Definition cpool_subsume_log (cpool : gset command) (log : list command) :=
    Forall (λ c, c ∈ cpool) log.

  Lemma log_cpool_incl γ gid log cpool :
    clog_half γ gid log -∗
    cpool_half γ gid cpool -∗
    ⌜cpool_subsume_log cpool log⌝.
  Admitted.

  Lemma log_update γ gid log cpool v :
    v ∈ cpool ->
    clog_half γ gid log -∗
    cpool_half γ gid cpool ==∗
    clog_half γ gid (log ++ [v]).
  Admitted.

  (* Global timestamp. *)
  Definition ts_auth γ (ts : nat) : iProp Σ.
  Admitted.

  Definition ts_lb γ (ts : nat) : iProp Σ.
  Admitted.

  #[global]
  Instance ts_lb_persistent γ ts :
    Persistent (ts_lb γ ts).
  Admitted.

  Definition txn_proph γ (acts : list action) : iProp Σ.
  Admitted.

End res.
