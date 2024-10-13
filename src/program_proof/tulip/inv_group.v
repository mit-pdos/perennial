From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list.
From Perennial.program_proof.tulip Require Import base res.

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
  { rewrite lookup_insert /tpls_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert |].
  }
  rewrite lookup_insert_ne; last done.
  rewrite /tpls_group map_filter_insert.
  by case_decide as H; first rewrite lookup_insert_ne.
Qed.

Definition prepared_impl_locked (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl) :=
  ∀ ts pwrs key,
  stm !! ts = Some (StPrepared pwrs) ->
  key ∈ dom pwrs ->
  ∃ tpl, tpls !! key = Some tpl ∧ tpl.2 = ts.

Definition locked_impl_prepared (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl) :=
  ∀ key tpl,
  tpls !! key = Some tpl ->
  tpl.2 ≠ O ->
  ∃ pwrs, stm !! tpl.2 = Some (StPrepared pwrs) ∧ key ∈ dom pwrs.

Section inv.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition safe_prepared γ gid ts pwrs : iProp Σ :=
    ∃ wrs, is_txn_wrs γ ts wrs ∧
           ⌜valid_ts ts ∧ valid_wrs wrs ∧ pwrs ≠ ∅ ∧ pwrs = wrs_group gid wrs⌝.

  (** The [StAborted] branch says that a transaction is aborted globally if it
  is aborted locally on some group (the other direction is encoded in
  [safe_submit]). This gives contradiction when learning a commit command under
  an aborted state. *)
  Definition safe_txnst γ gid ts st : iProp Σ :=
    match st with
    | StPrepared pwrs => is_group_prepared γ gid ts ∗ safe_prepared γ gid ts pwrs
    | StCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | StAborted => is_txn_aborted γ ts
    end.

  #[global]
  Instance safe_txnst_persistent γ gid ts st :
    Persistent (safe_txnst γ gid ts st).
  Proof. destruct st; apply _. Qed.

  Definition group_inv_no_log_no_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    ∃ (pm : gmap nat bool) (stm : gmap nat txnst) (tpls : gmap dbkey dbtpl),
      "Hpm"       ∷ own_group_prepm γ gid pm ∗
      "Hrepls"    ∷ ([∗ map] key ↦ tpl ∈ tpls_group gid tpls, own_repl_tuple_half γ key tpl) ∗
      "#Hsafestm" ∷ ([∗ map] ts ↦ st ∈ stm, safe_txnst γ gid ts st) ∗
      "%Hdompm"   ∷ ⌜dom pm ⊆ dom stm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked stm tpls⌝ ∗
      "%Hlip"     ∷ ⌜locked_impl_prepared stm tpls⌝.

  Definition group_inv_no_log_with_cpool
    γ (gid : groupid) (log : dblog) (cpool : gset command) : iProp Σ :=
    "Hcpool" ∷ own_txn_cpool_half γ gid cpool ∗
    "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_log γ (gid : groupid) (log : dblog) : iProp Σ :=
    ∃ (cpool : gset command),
      "Hcpool" ∷ own_txn_cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_cpool γ (gid : groupid) (cpool : gset command) : iProp Σ :=
    ∃ (log : dblog),
      "Hlog"   ∷ own_txn_log_half γ gid log ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv γ (gid : groupid) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset command),
      "Hlog"   ∷ own_txn_log_half γ gid log ∗
      "Hcpool" ∷ own_txn_cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

End inv.

Section lemma.
  Context `{!tulip_ghostG Σ}.

  Lemma group_inv_extract_log_expose_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ log cpool,
      own_txn_log_half γ gid log ∗
      group_inv_no_log_with_cpool γ gid log cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log_hide_cpool {γ gid} log cpool :
    own_txn_log_half γ gid log -∗
    group_inv_no_log_with_cpool γ gid log cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_log {γ} gid :
    group_inv γ gid -∗
    ∃ log,
      own_txn_log_half γ gid log ∗
      group_inv_no_log γ gid log.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_log {γ gid} log :
    own_txn_log_half γ gid log -∗
    group_inv_no_log γ gid log -∗
    group_inv γ gid.
  Proof. iIntros "Hlog Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_extract_cpool {γ} gid :
    group_inv γ gid -∗
    ∃ cpool,
      own_txn_cpool_half γ gid cpool ∗
      group_inv_no_cpool γ gid cpool.
  Proof. iIntros "Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

  Lemma group_inv_merge_cpool {γ gid} cpool :
    own_txn_cpool_half γ gid cpool -∗
    group_inv_no_cpool γ gid cpool -∗
    group_inv γ gid.
  Proof. iIntros "Hcpool Hgroup". iNamed "Hgroup". iFrame "∗ # %". Qed.

End lemma.
