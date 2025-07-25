From Perennial.program_proof Require Import grove_prelude.
From Perennial.program_proof.rsm.pure Require Import list quorum fin_maps fin_sets.
From Perennial.program_proof.tulip Require Import base cmd res stability.

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
  { rewrite lookup_insert_eq /tpls_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert_eq |].
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
  { rewrite lookup_insert_eq /filter_group.
    by rewrite (map_lookup_filter_Some_2 _ _ k tpl); [| rewrite lookup_insert_eq |].
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

  Definition quorum_voted γ (gid : u64) (ts rk : nat) (cid : coordid) : iProp Σ :=
    ∃ (ridsq : gset u64),
      ([∗ set] rid ∈ ridsq, is_replica_backup_vote γ gid rid ts rk cid) ∧
      ⌜cquorum rids_all ridsq⌝.
  
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

  Definition safe_txn_ptgs γ ts ptgs : iProp Σ :=
    ∃ wrs, is_txn_wrs γ ts wrs ∧ ⌜ptgs = ptgroups (dom wrs)⌝.

  Definition safe_backup_txn γ ts ptgs : iProp Σ :=
    ∃ wrs,
      "#Hwrs"   ∷ is_txn_wrs γ ts wrs ∗
      "%Hvts"   ∷ ⌜valid_ts ts⌝ ∗
      "%Hvwrs"  ∷ ⌜valid_wrs wrs⌝ ∗
      "%Hvptgs" ∷ ⌜ptgs = ptgroups (dom wrs)⌝.

  Lemma safe_txn_pwrs_ptgs_backup_txn γ gid ts pwrs ptgs :
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    safe_backup_txn γ ts ptgs.
  Proof.
    iIntros "Hpwrs Hptgs".
    iDestruct "Hpwrs" as (wrs1) "(Hwrs1 & %Hvt & %Hvw & _)".
    iDestruct "Hptgs" as (wrs2) "[Hwrs2 %Hptgs]".
    iDestruct (txn_wrs_agree with "Hwrs1 Hwrs2") as %->.
    iFrame "∗ %".
  Qed.

  Lemma safe_txn_pwrs_impl_is_txn_pwrs γ gid ts pwrs :
    safe_txn_pwrs γ gid ts pwrs -∗
    is_txn_pwrs γ gid ts pwrs.
  Proof.
    iIntros "Hsafe".
    iDestruct "Hsafe" as (wrs) "(Hwrs & _ & _ & _ & %Hpwrs)".
    by iFrame "Hwrs".
  Qed.

  Lemma safe_txn_pwrs_dom_pwrs γ gid ts pwrs :
    safe_txn_pwrs γ gid ts pwrs -∗
    ⌜dom pwrs ⊆ keys_all⌝.
  Proof.
    iIntros "Hsafe".
    iDestruct "Hsafe" as (wrs) "(Hwrs & _ & %Hvw & _ & %Hpwrs)".
    iPureIntro.
    trans (dom wrs); last apply Hvw.
    rewrite Hpwrs.
    apply dom_filter_subseteq.
  Qed.

  Lemma safe_txn_pwrs_impl_valid_ts γ gid ts pwrs :
    safe_txn_pwrs γ gid ts pwrs -∗
    ⌜valid_ts ts⌝.
  Proof. iIntros "Hsafe". by iDestruct "Hsafe" as (?) "(_ & ? & _ & _ & _)". Qed.

  Lemma safe_txn_pwrs_impl_valid_wrs γ gid ts pwrs :
    safe_txn_pwrs γ gid ts pwrs -∗
    ⌜valid_wrs pwrs⌝.
  Proof.
    iIntros "Hsafe".
    iDestruct "Hsafe" as (?) "(_ & _ & %Hvw & _ & %Hpwrs)".
    iPureIntro.
    rewrite Hpwrs.
    rewrite /valid_wrs.
    etrans; last apply Hvw.
    apply subseteq_dom, map_filter_subseteq.
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
           ⌜valid_ts ts⌝ ∗
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

  Definition is_group_prepare_proposal_if_classic γ gid ts rk p : iProp Σ :=
    (if decide (rk = O) then emp else is_group_prepare_proposal γ gid ts rk p)%I.

  #[global]
  Instance is_group_prepare_proposal_if_classic_persistent γ gid ts rk p :
    Persistent (is_group_prepare_proposal_if_classic γ gid ts rk p).
  Proof. rewrite /is_group_prepare_proposal_if_classic. case_decide; apply _. Defined.

  #[global]
  Instance is_group_prepare_proposal_if_classic_timeless γ gid ts rk p :
    Timeless (is_group_prepare_proposal_if_classic γ gid ts rk p).
  Proof. rewrite /is_group_prepare_proposal_if_classic. case_decide; apply _. Defined.

  (* NB: [safe_proposal] seems unnecessarily strong in that it always requires a
  classic quorum of responses, while sometimes a prepare proposal can be made
  even without a classic quorum (e.g., in a 3-node cluster, a transaction client
  should be able to choose to abort in the slow path immediately after receiving
  the first unprepare). This would not be a liveness issue (since liveness
  assumes a classic quorum of nodes to be alive), but might affect performance
  in certain cases. *)
  Definition safe_proposal γ gid (ts : nat) (rk : nat) (p : bool) : iProp Σ :=
    ∃ bsqlb : gmap u64 ballot,
      let n := latest_before_quorum rk bsqlb in
      "#Hlbs"     ∷ ([∗ map] rid ↦ l ∈ bsqlb, is_replica_ballot_lb γ gid rid ts l) ∗
      "#Hlatestc" ∷ is_group_prepare_proposal_if_classic γ gid ts n p ∗
      "%Hquorum"  ∷ ⌜cquorum rids_all (dom bsqlb)⌝ ∗
      "%Hlen"     ∷ ⌜map_Forall (λ _ l, (rk ≤ length l)%nat) bsqlb⌝ ∗
      "%Hlatestf" ∷ ⌜if decide (n = O) then size rids_all / 4 + 1 ≤ nfast bsqlb p else True⌝.

  Definition safe_proposals γ gid (ts : nat) (ps : gmap nat bool) : iProp Σ :=
    [∗ map] r ↦ p ∈ ps, safe_proposal γ gid ts r p.

  Definition safe_backup_token γ gid ts rk : iProp Σ :=
    ∃ cid ridsq,
      "Hexcl"    ∷ own_replica_backup_token γ cid.1 cid.2 ts rk gid ∗
      "#Hvotes"  ∷ ([∗ set] rid ∈ ridsq, is_replica_backup_vote γ gid rid ts rk cid) ∗
      "%Hquorum" ∷ ⌜cquorum rids_all ridsq⌝.

  Lemma safe_backup_token_excl γ gid ts rk :
    safe_backup_token γ gid ts rk -∗
    safe_backup_token γ gid ts rk -∗
    False.
  Proof.
    iIntros "Htk1 Htk2".
    iNamedSuffix "Htk1" "1".
    rename cid into cid1. rename ridsq into ridsq1.
    iNamedSuffix "Htk2" "2".
    rename cid into cid2. rename ridsq into ridsq2.
    (* Prove [cid1] = [cid2] using the quorum votes. *)
    pose proof (cquorums_overlapped _ _ _ Hquorum1 Hquorum2) as (x & Hq1 & Hq2).
    iDestruct (big_sepS_elem_of with "Hvotes1") as "Hvote1"; first apply Hq1.
    iDestruct (big_sepS_elem_of with "Hvotes2") as "Hvote2"; first apply Hq2.
    iDestruct (replica_backup_vote_agree with "Hvote1 Hvote2") as %->.
    (* Derive contradiction with exclusive backup token. *)
    iDestruct (replica_backup_token_excl with "Hexcl1 Hexcl2") as %[].
  Qed.

  Definition exclusive_proposal γ gid ts rk : iProp Σ :=
    if decide (rk = 1%nat)
    then own_txn_client_token γ ts gid
    else safe_backup_token γ gid ts rk.

  Lemma exclusive_proposal_excl γ gid ts rk :
    exclusive_proposal γ gid ts rk -∗
    exclusive_proposal γ gid ts rk -∗
    False.
  Proof.
    iIntros "Hexcl1 Hexcl2".
    rewrite /exclusive_proposal.
    case_decide.
    - iDestruct (txn_client_token_excl with "Hexcl1 Hexcl2") as %[].
    - iDestruct (safe_backup_token_excl with "Hexcl1 Hexcl2") as %[].
  Qed.

  Definition exclusive_proposals γ gid (ts : nat) (ps : gmap nat bool) : iProp Σ :=
    [∗ set] r ∈ dom ps, exclusive_proposal γ gid ts r.

  Definition group_inv_proposals_map γ gid : iProp Σ :=
    ∃ (psm : gmap nat (gmap nat bool)),
      "Hpsm"      ∷ own_group_prepare_proposals_map γ gid psm ∗
      "Hfresh"    ∷ ([∗ map] ts ↦ ps ∈ psm, exclusive_proposals γ gid ts ps) ∗
      "#Hsafepsm" ∷ ([∗ map] ts ↦ ps ∈ psm, safe_proposals γ gid ts ps) ∗
      (* TODO: program proof should also need "prepare proposed implies quorum-validated"  *)
      "%Hzunused" ∷ ⌜map_Forall (λ _ ps, ps !! O = None) psm⌝.

  Definition group_inv_no_log_no_cpool
    γ (gid : u64) (log : dblog) (cpool : gset ccommand) : iProp Σ :=
    ∃ (pm : gmap nat bool) (cm : gmap nat bool) (stm : gmap nat txnst)
      (hists : gmap dbkey dbhist) (tspreps : gmap dbkey nat),
      "Hpm"       ∷ own_group_prepm γ gid pm ∗
      "Hcm"       ∷ own_group_commit_map γ gid cm ∗
      "Hhists"    ∷ ([∗ map] k ↦ h ∈ filter_group gid hists, own_repl_hist_half γ k h) ∗
      "Hlocks"    ∷ ([∗ map] k ↦ t ∈ filter_group gid tspreps, own_repl_ts_half γ k t) ∗
      "Hpsm"      ∷ group_inv_proposals_map γ gid ∗
      "#Hsafestm" ∷ ([∗ map] ts ↦ st ∈ stm, safe_txnst γ gid ts st) ∗
      "#Hsafepm"  ∷ ([∗ map] ts ↦ p ∈ pm, safe_prepare γ gid ts p) ∗
      "#Hsafecp"  ∷ ([∗ set] c ∈ cpool, safe_submit γ gid c) ∗
      "%Hrsm"     ∷ ⌜apply_cmds log = State cm hists⌝ ∗
      "%Hpmstm"   ∷ ⌜map_Forall (λ t p, if p : bool then t ∈ dom stm else True) pm⌝ ∗
      "%Hdomptsm" ∷ ⌜dom tspreps = keys_all⌝ ∗
      "%Hcm"      ∷ ⌜cm = omap txnst_to_option_bool stm⌝ ∗
      "%Hpil"     ∷ ⌜prepared_impl_locked stm tspreps⌝ ∗
      "%Hlip"     ∷ ⌜locked_impl_prepared stm tspreps⌝ ∗
      "%Htsnz"    ∷ ⌜stm !! O = None⌝ ∗
      "%Hcscincl" ∷ ⌜txn_cpool_subsume_log cpool log⌝.

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

  #[global]
  Instance group_inv_timeless γ gid :
    Timeless (group_inv γ gid).
  Proof.
    rewrite /group_inv.
    repeat (apply exist_timeless => ?).
    repeat (apply sep_timeless; try apply _).
    rewrite /group_inv_no_log_no_cpool.
    repeat (apply exist_timeless => ?).
    repeat (apply sep_timeless; try apply _).
    - rewrite /group_inv_proposals_map.
      repeat (apply exist_timeless => ?).
      repeat (apply sep_timeless; try apply _).
      apply big_sepM_timeless. intros ???.
      rewrite /exclusive_proposals.
      apply big_sepS_timeless. intros y Hin.
      rewrite /exclusive_proposal.
      destruct (decide _); apply _.
    - apply big_sepM_timeless. intros x ??.
      rewrite /safe_txnst.
      destruct x; try apply _.
    - apply big_sepM_timeless. intros x y ?.
      rewrite /safe_prepare.
      rewrite /quorum_prepared/quorum_pdec/quorum_unprepared/quorum_validated/quorum_pdec.
      rewrite /quorum_pdec_at_rank.
      destruct y; try apply _.
    - apply big_sepS_timeless. intros x ?.
      rewrite /safe_submit.
      destruct x; try apply _.
  Qed.

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

  Definition group_histm_lbs_from_log γ gid log : iProp Σ :=
    match apply_cmds log with
    | State _ histm => ([∗ map] k ↦ h ∈ filter_group gid histm, is_repl_hist_lb γ k h)
    | _ => False
    end.

  #[global]
  Instance group_histm_lbs_from_log_persistent γ gid log :
    Persistent (group_histm_lbs_from_log γ gid log).
  Proof. rewrite /group_histm_lbs_from_log. destruct (apply_cmds log); apply _. Defined.

  Lemma group_inv_witness_group_histm_lbs_from_log {γ gid} loglb :
    is_txn_log_lb γ gid loglb -∗
    group_inv γ gid -∗
    group_histm_lbs_from_log γ gid loglb.
  Proof.
    iIntros "#Hloglb Hgroup".
    rewrite /group_histm_lbs_from_log.
    destruct (apply_cmds loglb) as [cmlb histmlb |] eqn:Happly; last first.
    { do 2 iNamed "Hgroup".
      iDestruct (txn_log_prefix with "Hlog Hloglb") as %Hprefix.
      unshelve epose proof (apply_cmds_not_stuck loglb _ Hprefix _) as Hns.
      { by rewrite Hrsm. }
      done.
    }
    iApply big_sepM_forall.
    iIntros (k h Hh).
    apply map_lookup_filter_Some in Hh as [Hh Hgid].
    iApply (group_inv_witness_repl_hist with "Hloglb Hgroup").
    { pose proof (apply_cmds_dom _ _ _ Happly) as Hdom.
      apply elem_of_dom_2 in Hh.
      set_solver.
    }
    { done. }
    { by rewrite /hist_from_log Happly. }
  Qed.

  Lemma group_inv_impl_valid_ccommand_cpool {γ gid} cpool :
    group_inv_no_cpool γ gid cpool -∗
    ⌜set_Forall (valid_ccommand gid) cpool⌝.
  Proof.
    iIntros "Hgroup".
    do 2 iNamed "Hgroup".
    iIntros (c Hc).
    iDestruct (big_sepS_elem_of with "Hsafecp") as "Hsafec"; first apply Hc.
    destruct c; simpl.
    { iDestruct "Hsafec" as (wrs) "(_ & _ & %Hvts & %Hwg & %Hgid & %Hvw)".
      iPureIntro.
      split; first done.
      rewrite /valid_pwrs Hwg wrs_group_keys_group_dom.
      rewrite /valid_wrs in Hvw.
      rewrite /keys_group.
      (* [set_solver] is able to solve this directly when [key_to_group] is
      admitted, but is unable to solve this after it is defined, so we apply an
      additional lemma [filter_subseteq_mono]. *)
      (* set_solver. *)
      by apply filter_subseteq_mono.
    }
    { by iDestruct "Hsafec" as "[_ %Hvts]". }
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

  Lemma group_inv_impl_valid_ccommand_log {γ gid} loglb :
    is_txn_log_lb γ gid loglb -∗
    group_inv γ gid -∗
    ⌜Forall (valid_ccommand gid) loglb⌝.
  Proof.
    iIntros "#Hlb Hinv".
    iDestruct (group_inv_extract_cpool with "Hinv") as (cpool) "[Hcpool Hinv]".
    iDestruct (group_inv_impl_valid_ccommand_cpool with "Hinv") as %Hvcmds.
    iNamed "Hinv".
    iDestruct (txn_log_prefix with "Hlog Hlb") as %Hprefix.
    iNamed "Hgroup".
    iPureIntro.
    rewrite /txn_cpool_subsume_log Forall_forall in Hcscincl.
    rewrite Forall_forall.
    intros cmd Hcmd.
    by apply Hvcmds, Hcscincl, (elem_of_prefix loglb).
  Qed.

End lemma.
