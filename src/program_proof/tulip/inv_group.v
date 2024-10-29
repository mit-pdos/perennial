From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list quorum fin_maps.
From Perennial.program_proof.tulip Require Import base cmd res.

Lemma tpls_group_keys_group_dom gid tpls :
  dom (tpls_group gid tpls) = keys_group gid (dom tpls).
Proof. by rewrite /tpls_group /keys_group filter_dom_L. Qed.

Lemma wrs_group_keys_group_dom gid wrs :
  dom (wrs_group gid wrs) = keys_group gid (dom wrs).
Proof. by rewrite /wrs_group /keys_group filter_dom_L. Qed.

Lemma filter_group_keys_group_dom `{Countable A} gid (m : gmap dbkey A) :
  dom (filter_group gid m) = keys_group gid (dom m).
Proof. by rewrite /filter_group /keys_group filter_dom_L. Qed.

(* TODO: cleanup lemmas about [tpls_group]. *)

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
  by case_decide; first rewrite lookup_insert_ne.
Qed.

Lemma key_to_group_filter_group `{Countable A} key gid (m : gmap dbkey A) :
  key ∈ dom (filter_group gid m) ->
  key_to_group key = gid.
Proof. intros Hdom. rewrite filter_group_keys_group_dom in Hdom. set_solver. Qed.

Lemma lookup_filter_group_key_to_group `{Countable A} k v (m : gmap dbkey A) :
  m !! k = Some v ->
  filter_group (key_to_group k) m !! k = Some v.
Proof. intros Hv. by apply map_lookup_filter_Some_2. Qed.

Lemma filter_group_dom `{Countable A} gid (m1 m2 : gmap dbkey A) :
  dom m1 = dom m2 ->
  dom (filter_group gid m1) = dom (filter_group gid m2).
Proof. intros Hdom. by rewrite 2!filter_group_keys_group_dom Hdom. Qed.

Lemma insert_filter_group_commute `{Countable A} key tpl gid (m : gmap dbkey A) :
  key_to_group key = gid ->
  <[key := tpl]> (filter_group gid m) = filter_group gid (<[key := tpl]> m).
Proof.
  intros Hgid.
  apply map_eq. intros k.
  destruct (decide (key = k)) as [-> | Hne].
  { rewrite lookup_insert /filter_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert |].
  }
  rewrite lookup_insert_ne; last done.
  rewrite /filter_group map_filter_insert.
  by case_decide; first rewrite lookup_insert_ne.
Qed.

Definition prepared_impl_locked (stm : gmap nat txnst) (tss : gmap dbkey nat) :=
  ∀ ts pwrs key,
  stm !! ts = Some (StPrepared pwrs) ->
  key ∈ dom pwrs ->
  tss !! key = Some ts.

Definition locked_impl_prepared (stm : gmap nat txnst) (tss : gmap dbkey nat) :=
  ∀ key ts,
  tss !! key = Some ts ->
  ts ≠ O ->
  ∃ pwrs, stm !! ts = Some (StPrepared pwrs) ∧ key ∈ dom pwrs.

Section inv.
  Context `{!tulip_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : tulip_names).

  Definition quorum_validated γ (gid : u64) (ts : nat) : iProp Σ :=
    ∃ (ridsq : gset u64),
      ([∗ set] rid ∈ ridsq, is_replica_validated_ts γ gid rid ts) ∧
      ⌜cquorum rids_all ridsq⌝.

  Definition quorum_fast_pdec γ (gid : u64) (ts : nat) (p : bool) : iProp Σ :=
    ∃ (ridsq : gset u64),
      ([∗ set] rid ∈ ridsq, is_replica_pdec_at_rank γ gid rid ts O p) ∗
      ⌜fquorum rids_all ridsq⌝.

  Definition quorum_classic_pdec γ (gid : u64) (ts rank : nat) (p : bool) : iProp Σ :=
    ∃ (ridsq : gset u64),
      ([∗ set] rid ∈ ridsq, is_replica_pdec_at_rank γ gid rid ts rank p) ∗
      ⌜cquorum rids_all ridsq⌝.

  Definition quorum_pdec_at_rank γ (gid : u64) (ts rank : nat) (p : bool) : iProp Σ :=
    if decide (rank = O)
    then quorum_fast_pdec γ gid ts p
    else quorum_classic_pdec γ gid ts rank p.

  #[global]
  Instance quorum_pdec_at_rank_persistent γ gid ts rank p :
    Persistent (quorum_pdec_at_rank γ gid ts rank p).
  Proof. rewrite /quorum_pdec_at_rank. case_decide; apply _. Defined.

  Definition quorum_pdec γ (gid : u64) (ts : nat) (p : bool) : iProp Σ :=
    ∃ rank, quorum_pdec_at_rank γ gid ts rank p.

  Definition quorum_prepared γ (gid : u64) (ts : nat) : iProp Σ :=
    quorum_pdec γ gid ts true.

  Definition quorum_unprepared γ (gid : u64) (ts : nat) : iProp Σ :=
    quorum_pdec γ gid ts false.

  Definition is_txn_pwrs γ gid ts pwrs : iProp Σ :=
    ∃ wrs, is_txn_wrs γ ts wrs ∧ ⌜pwrs = wrs_group gid wrs⌝.

  Lemma txn_pwrs_agree γ gid ts pwrs1 pwrs2 :
    is_txn_pwrs γ gid ts pwrs1 -∗
    is_txn_pwrs γ gid ts pwrs2 -∗
    ⌜pwrs2 = pwrs1⌝.
  Proof.
    iIntros "Hpwrs1 Hpwrs2".
    iDestruct "Hpwrs1" as (wrs1) "[Hwrs1 %Hpwrs1]".
    iDestruct "Hpwrs2" as (wrs2) "[Hwrs2 %Hpwrs2]".
    iDestruct (txn_wrs_agree with "Hwrs1 Hwrs2") as %->.
    by rewrite Hpwrs1.
  Qed.

  Definition safe_txn_pwrs γ gid ts pwrs : iProp Σ :=
    ∃ wrs, is_txn_wrs γ ts wrs ∧
           ⌜valid_ts ts ∧ valid_wrs wrs ∧ pwrs ≠ ∅ ∧ pwrs = wrs_group gid wrs⌝.

  Lemma safe_txn_pwrs_impl_is_txn_pwrs γ gid ts pwrs :
    safe_txn_pwrs γ gid ts pwrs -∗
    is_txn_pwrs γ gid ts pwrs.
  Proof.
    iIntros "Hsafe".
    iDestruct "Hsafe" as (wrs) "(Hwrs & _ & _ & _ & %Hpwrs)".
    by iFrame "Hwrs".
  Qed.

  (** The [StAborted] branch says that a transaction is aborted globally if it
  is aborted locally on some group (the other direction is encoded in
  [safe_submit]). This gives contradiction when learning a commit command under
  an aborted state. *)
  Definition safe_txnst γ gid ts st : iProp Σ :=
    match st with
    | StPrepared pwrs => is_group_prepared γ gid ts ∗ safe_txn_pwrs γ gid ts pwrs
    | StCommitted => (∃ wrs, is_txn_committed γ ts wrs)
    | StAborted => is_txn_aborted γ ts
    end.

  #[global]
  Instance safe_txnst_persistent γ gid ts st :
    Persistent (safe_txnst γ gid ts st).
  Proof. destruct st; apply _. Defined.

  Definition safe_prepare γ gid ts prep : iProp Σ :=
    match prep with
    | true  => quorum_prepared γ gid ts ∗ quorum_validated γ gid ts
    | false => quorum_unprepared γ gid ts
    end.

  #[global]
  Instance safe_prepare_persistent γ gid ts p :
    Persistent (safe_prepare γ gid ts p).
  Proof. destruct p; apply _. Defined.

  Definition safe_commit γ gid ts pwrs : iProp Σ :=
    ∃ wrs, is_txn_committed γ ts wrs ∗
           is_txn_wrs γ ts wrs ∗
           ⌜pwrs = wrs_group gid wrs⌝ ∗
           ⌜gid ∈ ptgroups (dom wrs)⌝ ∗
           ⌜valid_wrs wrs⌝.

  Definition safe_abort γ ts : iProp Σ :=
    is_txn_aborted γ ts ∧ ⌜valid_ts ts⌝.

  Definition safe_submit γ gid c : iProp Σ :=
    match c with
    | CmdCommit ts pwrs => safe_commit γ gid ts pwrs
    | CmdAbort ts => safe_abort γ ts
    end.

  #[global]
  Instance safe_submit_persistent γ gid c :
    Persistent (safe_submit γ gid c).
  Proof. destruct c; apply _. Defined.

  Definition txnst_to_option_bool (st : txnst) :=
    match st with
    | StPrepared _ => None
    | StCommitted => Some true
    | StAborted => Some false
    end.

  Definition group_inv_no_log_no_cpool
    γ (gid : u64) (log : dblog) (cpool : gset ccommand) : iProp Σ :=
    ∃ (pm : gmap nat bool) (cm : gmap nat bool) (stm : gmap nat txnst)
      (hists : gmap dbkey dbhist) (tspreps : gmap dbkey nat),
      "Hpm"       ∷ own_group_prepm γ gid pm ∗
      "Hcm"       ∷ own_group_commit_map γ gid cm ∗
      "Hhists"    ∷ ([∗ map] k ↦ h ∈ filter_group gid hists, own_repl_hist_half γ k h) ∗
      "Hlocks"    ∷ ([∗ map] k ↦ t ∈ filter_group gid tspreps, own_repl_ts_half γ k t) ∗
      "#Hsafestm" ∷ ([∗ map] ts ↦ st ∈ stm, safe_txnst γ gid ts st) ∗
      "#Hsafepm"  ∷ ([∗ map] ts ↦ p ∈ pm, safe_prepare γ gid ts p) ∗
      "#Hsafecp"  ∷ ([∗ set] c ∈ cpool, safe_submit γ gid c) ∗
      "%Hrsm"     ∷ ⌜apply_cmds log = State cm hists⌝ ∗
      "%Hdompm"   ∷ ⌜dom pm ⊆ dom stm⌝ ∗
      "%Hdomptsm" ∷ ⌜dom tspreps = keys_all⌝ ∗
      "%Hcm"      ∷ ⌜cm = omap txnst_to_option_bool stm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked stm tspreps⌝ ∗
      "%Hlip"     ∷ ⌜locked_impl_prepared stm tspreps⌝ ∗
      "%Htsnz"    ∷ ⌜stm !! O = None⌝.

  Definition group_inv_no_log_with_cpool
    γ (gid : u64) (log : dblog) (cpool : gset ccommand) : iProp Σ :=
    "Hcpool" ∷ own_txn_cpool_half γ gid cpool ∗
    "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_log
    γ (gid : u64) (log : dblog) : iProp Σ :=
    ∃ (cpool : gset ccommand),
      "Hcpool" ∷ own_txn_cpool_half γ gid cpool ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv_no_cpool
    γ (gid : u64) (cpool : gset ccommand) : iProp Σ :=
    ∃ (log : dblog),
      "Hlog"   ∷ own_txn_log_half γ gid log ∗
      "Hgroup" ∷ group_inv_no_log_no_cpool γ gid log cpool.

  Definition group_inv γ (gid : u64) : iProp Σ :=
    ∃ (log : dblog) (cpool : gset ccommand),
      "Hlog"    ∷ own_txn_log_half γ gid log ∗
      "Hcpool"  ∷ own_txn_cpool_half γ gid cpool ∗
      "Hgroup"  ∷ group_inv_no_log_no_cpool γ gid log cpool.

End inv.

Section lemma.
  Context `{!tulip_ghostG Σ}.

  Definition hist_from_log log key hist :=
    match apply_cmds log with
    | State _ histm => histm !! key = Some hist
    | _ => False
    end.

  Lemma group_inv_witness_repl_hist {γ gid loglb} key hlb :
    valid_key key ->
    key_to_group key = gid ->
    hist_from_log loglb key hlb ->
    is_txn_log_lb γ gid loglb -∗
    group_inv γ gid -∗
    is_repl_hist_lb γ key hlb.
  Proof.
    iIntros (Hkey Hgid Hhlb) "#Hloglb Hgroup".
    do 2 iNamed "Hgroup".
    pose proof (apply_cmds_dom _ _ _ Hrsm) as Hdom.
    assert (is_Some (hists !! key)) as [h Hh].
    { rewrite -elem_of_dom. set_solver. }
    iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
    rewrite /hist_from_log in Hhlb.
    destruct (apply_cmds loglb) as [cmlb histmlb |] eqn:Happly; last done.
    pose proof (apply_cmds_mono_histm Hprefix Hrsm Happly) as Hprefixes.
    pose proof (map_Forall2_lookup_Some _ _ _ _ _ _ Hh Hhlb Hprefixes) as Hprefixh.
    simpl in Hprefixh.
    iDestruct (big_sepM_lookup _ _ key h with "Hhists") as "Hhist".
    { by rewrite map_lookup_filter_Some. }
    iDestruct (repl_hist_witness with "Hhist") as "#Hhistlb".
    iApply (repl_hist_lb_weaken hlb with "Hhistlb").
    apply Hprefixh.
  Qed.

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
