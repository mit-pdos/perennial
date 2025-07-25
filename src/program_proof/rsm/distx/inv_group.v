From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.distx Require Import base res cmd.
From Perennial.program_proof.rsm.pure Require Import list.

Lemma tpls_group_keys_group_dom gid tpls :
  dom (tpls_group gid tpls) = keys_group gid (dom tpls).
Proof. by rewrite /tpls_group /keys_group filter_dom_L. Qed.

Lemma wrs_group_keys_group_dom gid wrs :
  dom (wrs_group gid wrs) = keys_group gid (dom wrs).
Proof. by rewrite /wrs_group /keys_group filter_dom_L. Qed.

Lemma key_to_group_tpls_group key gid tpls :
  key ∈ dom (tpls_group gid tpls) ->
  key_to_group key = gid.
Proof. intros Hdom. rewrite tpls_group_keys_group_dom in Hdom. set_solver. Qed.

Lemma tpls_group_dom {gid tpls0 tpls1} :
  dom tpls0 = dom tpls1 ->
  dom (tpls_group gid tpls0) = dom (tpls_group gid tpls1).
Proof. intros Hdom. by rewrite 2!tpls_group_keys_group_dom Hdom. Qed.

Lemma insert_tpls_group_commute key tpl tpls gid :
  key_to_group key = gid ->
  <[key := tpl]> (tpls_group gid tpls) = tpls_group gid (<[key := tpl]> tpls).
Proof.
  intros Hgid.
  apply map_eq. intros k.
  destruct (decide (key = k)) as [-> | Hne].
  { rewrite lookup_insert_eq /tpls_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert_eq |].
  }
  rewrite lookup_insert_ne; last done.
  rewrite /tpls_group map_filter_insert.
  by case_decide as H; first rewrite lookup_insert_ne.
Qed.

(** Global per-group invariant. *)

Section inv.
  Context `{!distx_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : distx_names).

  (** The [StAborted] branch says that a transaction is aborted globally if it
  is aborted locally on some replica (the other direction is encoded in
  [safe_submit]). This gives contradiction when learning a commit command under
  an aborted state. *)
  Definition txn_token γ gid ts st : iProp Σ :=
    match st with
    | StPrepared _ => txnprep_prep γ gid ts
    | StCommitted => (∃ wrs, txnres_cmt γ ts wrs)
    | StAborted => txnres_abt γ ts
    end.

  #[global]
    Instance txn_token_persistent γ gid ts st :
    Persistent (txn_token γ gid ts st).
  Proof. destruct st; apply _. Qed.

  Definition txn_tokens γ gid log : iProp Σ :=
    ∀ logp stm tpls,
    ⌜prefix logp log⌝ -∗
    ⌜apply_cmds logp = State stm tpls⌝ -∗
    ([∗ map] ts ↦ st ∈ stm, txn_token γ gid ts st)%I.

  Definition hist_repl_witnesses γ gid log : iProp Σ :=
    ∀ logp stm tpls,
    ⌜prefix logp log⌝ -∗
    ⌜apply_cmds logp = State stm tpls⌝ -∗
    ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, hist_repl_lb γ key tpl.1)%I.

  Definition safe_read gid ts key :=
    valid_ts ts ∧ valid_key key ∧ key_to_group key = gid.

  (* TODO: [valid_ts ts ∧ valid_wrs wrs] should be redundant with the of
  constraint [Hwrsm] in [txnsys_inv]. *)
  Definition safe_prepare γ gid ts pwrs : iProp Σ :=
    ∃ wrs, txnwrs_receipt γ ts wrs ∧
           ⌜valid_ts ts ∧ valid_wrs wrs ∧ pwrs ≠ ∅ ∧ pwrs = wrs_group gid wrs⌝.

  Definition safe_commit γ gid ts : iProp Σ :=
    ∃ wrs, txnres_cmt γ ts wrs ∧ ⌜valid_ts ts ∧ gid ∈ ptgroups (dom wrs)⌝.

  Definition safe_abort γ ts : iProp Σ :=
    txnres_abt γ ts ∧ ⌜valid_ts ts⌝.

  Definition safe_submit γ gid (c : command) : iProp Σ :=
    match c with
    | CmdRead ts key => ⌜safe_read gid ts key⌝
    (* Enforces [CmdPrep] is submitted to only participant groups, and partial
    writes is part of the global commit, which we would likely need with
    coordinator recovery. *)
    | CmdPrep ts pwrs => safe_prepare γ gid ts pwrs
    (* Enforces [CmdCmt] is submitted to only participant groups. *)
    | CmdCmt ts => safe_commit γ gid ts
    | CmdAbt ts => safe_abort γ ts
    end.

  #[global]
    Instance safe_submit_persistent γ gid c :
    Persistent (safe_submit γ gid c).
  Proof. destruct c; apply _. Qed.

  Definition valid_prepared γ gid ts st : iProp Σ :=
    match st with
    | StPrepared pwrs => safe_prepare γ gid ts pwrs
    | _ => True
    end.

  #[global]
    Instance valid_prepared_persistent γ gid ts st :
    Persistent (valid_prepared γ gid ts st).
  Proof. destruct st; apply _. Qed.

  Definition group_inv_no_log_no_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    ∃ (pm : gmap nat bool) (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hpm"     ∷ txnprep_auth γ gid pm ∗
      "Hrepls"  ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, tuple_repl_half γ key tpl) ∗
      "#Htks"   ∷ txn_tokens γ gid log ∗
      "#Hhists" ∷ hist_repl_witnesses γ gid log ∗
      "#Hvp"    ∷ ([∗ map] ts ↦ st ∈ stm, valid_prepared γ gid ts st) ∗
      "#Hvc"    ∷ ([∗ set] c ∈ cpool, safe_submit γ gid c) ∗
      "%Hrsm"   ∷ ⌜apply_cmds log = State stm tpls⌝ ∗
      "%Hdompm" ∷ ⌜dom pm ⊆ dom stm⌝.

  Definition group_inv_no_log_with_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    "Hcpool" ∷ cpool_half γ gid cpool ∗
    "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_log γ (gid : groupid) (log : dblog) : iProp Σ :=
    ∃ (cpool : gset command),
      "Hcpool" ∷ cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_cpool γ (gid : groupid) (cpool : gset command) : iProp Σ :=
    ∃ (log : dblog),
      "Hlog"   ∷ clog_half γ gid log ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset command),
      "Hlog"   ∷ clog_half γ gid log ∗
      "Hcpool" ∷ cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

End inv.

Section lemma.
  Context `{!distx_ghostG Σ}.

  Lemma group_inv_extract_log_expose_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ log cpool,
      clog_half γ gid log ∗
      group_inv_no_log_with_cpool γ gid log cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log_hide_cpool {γ gid} log cpool :
    clog_half γ gid log -∗
    group_inv_no_log_with_cpool γ gid log cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_log {γ} gid :
    group_inv γ gid -∗
    ∃ log,
      clog_half γ gid log ∗
      group_inv_no_log γ gid log.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log {γ gid} log :
    clog_half γ gid log -∗
    group_inv_no_log γ gid log -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ cpool,
      cpool_half γ gid cpool ∗
      group_inv_no_cpool γ gid cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_cpool {γ gid} cpool :
    cpool_half γ gid cpool -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hcpool Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma hist_repl_witnesses_inv_learn {γ gid log stm tpls} c :
    apply_cmds (log ++ [c]) = State stm tpls ->
    ([∗ map] k ↦ t ∈ tpls_group gid tpls, tuple_repl_half γ k t) -∗
    hist_repl_witnesses γ gid log -∗
    hist_repl_witnesses γ gid (log ++ [c]).
  Proof.
    iIntros (Hrsm) "Hrepls Hwns".
    iIntros (logp stmp tplsp Hprefix Hrsmp).
    destruct (prefix_snoc _ _ _ Hprefix) as [Hlogp | ->].
    { by iApply "Hwns". }
    rewrite Hrsmp in Hrsm. inversion Hrsm. subst tplsp.
    iApply (big_sepM_mono with "Hrepls").
    iIntros (k x _) "[Hhist Hts]".
    iApply (hist_repl_witness with "Hhist").
  Qed.

  Lemma group_inv_no_log_witness_txn_token {γ gid log} loga stm tpls ts st :
    prefix loga log ->
    apply_cmds loga = State stm tpls ->
    stm !! ts = Some st ->
    group_inv_no_log γ gid log -∗
    txn_token γ gid ts st.
  Proof.
    iIntros (Hprefix Hrsm Hstm) "Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct ("Htks" with "[] []") as "Htkm".
    { iPureIntro. apply Hprefix. }
    { iPureIntro. apply Hrsm. }
    by iDestruct (big_sepM_lookup with "Htkm") as "Htk"; first apply Hstm.
  Qed.

  Lemma group_inv_no_log_witness_hist_repl_lb {γ gid log} loga stm tpls key tpl :
    prefix loga log ->
    apply_cmds loga = State stm tpls ->
    tpls !! key = Some tpl ->
    key_to_group key = gid ->
    group_inv_no_log γ gid log -∗
    hist_repl_lb γ key tpl.1.
  Proof.
    iIntros (Hprefix Hrsm Htpls Hgid) "Hgroup".
    do 2 iNamed "Hgroup".
    iDestruct ("Hhists" with "[] []") as "Hhistm".
    { iPureIntro. apply Hprefix. }
    { iPureIntro. apply Hrsm. }
    iDestruct (big_sepM_lookup with "Hhistm") as "Hhist"; last done.
    by rewrite /tpls_group map_lookup_filter_Some.
  Qed.

  Lemma group_inv_no_log_witness_hist_repl_lbs {γ gid log} loga stm tpls :
    prefix loga log ->
    apply_cmds loga = State stm tpls ->
    group_inv_no_log γ gid log -∗
    [∗ map] key ↦ tpl ∈ tpls_group gid tpls, hist_repl_lb γ key tpl.1.
  Proof.
    iIntros (Hprefix Hrsm) "Hgroup".
    iApply big_sepM_forall.
    iIntros (k t Hkt).
    rewrite map_lookup_filter_Some in Hkt.
    destruct Hkt as [Hkt Hgid].
    by iApply group_inv_no_log_witness_hist_repl_lb.
  Qed.

End lemma.
