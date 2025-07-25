From RecordUpdate Require Import RecordUpdate.

From Perennial.Helpers Require Import range_set.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.
From Perennial.goose_lang Require Import crash_modality.
From Perennial.goose_lang Require recovery_lifting.
From Perennial.program_proof Require Import wal.logger_proof.
From Perennial.program_proof Require Import wal.installer_proof.

Section goose_lang.
Context `{!heapGS Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (dinit: disk).
Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Definition wal_init_ghost_state (γnew: wal_names) : iProp Σ :=
    "installer_pos" ∷ ghost_var γnew.(installer_pos_name) 1 0%nat ∗
    "installer_txn_id" ∷ ghost_var γnew.(installer_txn_id_name) 1 0%nat ∗

    "installer_pos_mem" ∷ ghost_var γnew.(installer_pos_mem_name) 1 (W64 0) ∗
    "installer_txn_id_mem" ∷ ghost_var γnew.(installer_txn_id_mem_name) 1 0%nat ∗

    "logger_pos" ∷ ghost_var γnew.(logger_pos_name) 1 (W64 0) ∗
    "logger_txn_id" ∷ ghost_var γnew.(logger_txn_id_name) 1 0%nat ∗

    "installed_pos_mem" ∷ ghost_var γnew.(installed_pos_mem_name) 1 (W64 0) ∗
    "installed_txn_id_mem" ∷ ghost_var γnew.(installed_txn_id_mem_name) 1 0%nat ∗

    "diskEnd" ∷ ghost_var γnew.(diskEnd_name) 1 0%nat ∗
    "diskEnd_txn_id" ∷ ghost_var γnew.(diskEnd_txn_id_name) 1 0%nat ∗

    "diskEnd_mem" ∷ mono_nat_auth_own γnew.(diskEnd_mem_name) 1 0%nat ∗
    "diskEnd_mem_txn_id" ∷ mono_nat_auth_own γnew.(diskEnd_mem_txn_id_name) 1 0%nat ∗
    "being_installed_start_txn" ∷ mono_nat_auth_own γnew.(being_installed_start_txn_name) 1 0%nat ∗
    "already_installed" ∷ ghost_var γnew.(already_installed_name) 1 ([] : list update.t)  ∗
    "stable_txn_ids" ∷ map_ctx γnew.(stable_txn_ids_name) 1 (∅ : gmap nat unit) ∗
    "txns_ctx" ∷ txns_ctx γnew [] ∗
    "start_avail" ∷ thread_own γnew.(start_avail_name) Available ∗
    "start_avail_ctx" ∷ thread_own_ctx γnew.(start_avail_name) True ∗
    "diskEnd_avail" ∷ thread_own γnew.(diskEnd_avail_name) Available ∗
    "diskEnd_avail_ctx" ∷ thread_own_ctx γnew.(diskEnd_avail_name) True ∗
    "cs" ∷ ghost_var γnew.(cs_name) 1 (inhabitant : circΣ.t) ∗
    "txns" ∷ ghost_var γnew.(txns_name) 1 ([] : list (u64 * list update.t))
.

Definition is_wal_inner_crash (γold: wal_names) s' : iProp Σ := True.

Definition wal_ghost_exchange (γold γnew: wal_names) : iProp Σ := True.

(* This is produced by recovery as a post condition, can be used to get is_wal *)
Definition is_wal_inv_pre (l: loc) γ s (dinit : disk) : iProp Σ :=
  is_wal_inner l γ s dinit ∗ (∃ cs, is_circular_state γ.(circ_name) cs ∗ circular_pred γ cs).

Existing Instance own_into_crash.

Definition log_crash_to σ diskEnd_txn_id :=
  set log_state.durable_lb (λ _, diskEnd_txn_id)
      (set log_state.txns (take (S diskEnd_txn_id)) σ).

Lemma crash_to_diskEnd γ cs σ diskEnd_txn_id installed_txn_id installer_txn_id :
  is_durable_txn (Σ:=Σ) γ cs σ.(log_state.txns) diskEnd_txn_id  σ.(log_state.durable_lb) -∗
  is_durable γ cs σ.(log_state.txns) installed_txn_id installer_txn_id diskEnd_txn_id -∗
  ⌜relation.denote log_crash σ
    (log_crash_to σ (σ.(log_state.durable_lb) `max` diskEnd_txn_id))%nat
  tt⌝.
Proof.
  iNamed 1.
  rewrite /is_durable.
  iNamed 1.
  iPureIntro.
  simpl.
  eexists _ (σ.(log_state.durable_lb) `max` diskEnd_txn_id)%nat;
    simpl; monad_simpl.
  constructor.
  split; try lia.
  apply is_txn_bound in Hend_txn.
  lia.
Qed.

Lemma concat_mono {A: Type} (l1 l2: list (list A)):
  incl l1 l2 →
  incl (concat l1) (concat l2).
Proof. intros Hincl a. rewrite ?in_concat. naive_solver. Qed.

Lemma take_incl {A} (l: list A) n:
  incl (take n l) l.
Proof. intros a. rewrite -{2}(firstn_skipn n l) in_app_iff. auto. Qed.

Lemma fmap_incl {A B} (f: A → B) (l l': list A):
  incl l l' →
  incl (fmap f l) (fmap f l').
Proof.
  intros Hincl a. rewrite -?list_elem_of_In.
  intros (?&?&Hin')%list_elem_of_fmap. subst.
  apply list_elem_of_fmap. eexists; split; eauto.
  move: Hin'. rewrite ?list_elem_of_In. eauto.
Qed.

Lemma log_crash_to_wf σ σ' x :
  wal_wf σ →
  relation.denote log_crash σ σ' x →
  wal_wf σ'.
Proof.
  clear P.
  simpl.
  intros Hwf Htrans; monad_inv.
  destruct Hwf as (Haddrs&Hmono&Hb1&hb2).
  split_and!; simpl.
  - rewrite /log_state.updates; simpl.
    eapply incl_Forall; eauto.
    apply concat_mono, fmap_incl, take_incl.
  - move: Hmono.
    rewrite -{1}(firstn_skipn (S crash_txn) (σ.(log_state.txns))).
    rewrite fmap_app list_mono_app; naive_solver.
  - lia.
  - len.
Qed.

Lemma log_crash_to_post_crash σ σ' x :
  relation.denote log_crash σ σ' x →
  wal_post_crash σ'.
Proof.
  simpl.
  intros Htrans; monad_inv.
  rewrite /wal_post_crash //=.
  rewrite length_take. lia.
Qed.

Lemma is_txn_implies_non_empty_txns γ cs txns installed_txn_id:
  is_txn txns installed_txn_id (start cs) →
  txns ≠ [].
Proof.
  rewrite /is_txn.
  rewrite fmap_Some.
  intros (?&Hlookup&_).
  apply list_elem_of_lookup_2 in Hlookup.
  destruct txns; eauto.
  set_solver.
Qed.

(* XXX: I think this suggests that we're going to have to require the initial state
   to have a non empty list of txns. *)
Lemma is_installed_txn_implies_non_empty_txns γ cs txns installed_txn_id lb:
  is_installed_txn (Σ:=Σ) γ cs txns installed_txn_id lb -∗
  ⌜ txns ≠ [] ⌝.
Proof. iNamed 1. iPureIntro. by eapply is_txn_implies_non_empty_txns. Qed.

Lemma circ_matches_txns_crash diskEnd cs txns installed_txn_id installer_pos installer_txn_id
      diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id :
  diskEnd = Z.to_nat (circΣ.diskEnd cs) →
  circ_matches_txns cs txns
                    installed_txn_id installer_pos installer_txn_id
                    diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id →
  circ_matches_txns cs (take (S diskEnd_txn_id) txns)
                    installed_txn_id installer_pos installer_txn_id
                    diskEnd diskEnd_txn_id diskEnd_txn_id.
Proof.
  intros ->.
  rewrite /circ_matches_txns.
  intros Hcirc.
  apply is_memLog_boundaries_take_txns; first by reflexivity.
  replace (Z.to_nat (circΣ.diskEnd cs) - uint.nat (start cs))%nat
    with (length (upds cs)) by (rewrite /circΣ.diskEnd; word).
  eapply (is_memLog_boundaries_move _ _ _ pmwrb_de) in Hcirc.
  2: reflexivity.
  assumption.
Qed.

Lemma is_txn_from_take_is_txn n txns id pos:
  is_txn (take n txns) id pos →
  is_txn txns id pos.
Proof.
  rewrite /is_txn.
  destruct (decide (id < n)%nat).
  { by rewrite -> lookup_take_lt by lia. }
  rewrite -> lookup_take_ge by lia.
  inversion 1.
Qed.

Hint Unfold circ_matches_txns : word.

Lemma lookup_take_Some {A: Type} (l: list A) (n i: nat) a:
  (take n l !! i = Some a) → (i < n)%nat.
Proof.
  intros His_Some.
  apply not_ge => Hge.
  rewrite lookup_take_ge in His_Some; auto; congruence.
Qed.

Lemma is_txn_take txns txn_id pos :
  is_txn txns txn_id pos →
  is_txn (take (S txn_id) txns) txn_id pos.
Proof.
  rewrite /is_txn. intro Hlook.
  rewrite -> lookup_take_lt by lia; auto.
Qed.

Lemma is_highest_txn_take txns txn_id pos :
  is_highest_txn txns txn_id pos →
  is_highest_txn (take (S txn_id) txns) txn_id pos.
Proof.
  rewrite /is_highest_txn /is_txn. intros (Hlook&Hle); split.
  - rewrite -> lookup_take_lt by lia; auto.
  - intros txn_id'. rewrite ?fmap_Some.
    intros (x&Hlookup&Hpos); subst.
    eapply lookup_take_Some in Hlookup; lia.
Qed.

Lemma alloc_wal_init_ghost_state γ γcirc :
  ⊢ |==> ∃ γnew, "%Hbase_name" ∷ ⌜γnew.(base_disk_name) = γ.(base_disk_name)⌝ ∗
                 "%Hcirc_name" ∷ ⌜γnew.(circ_name) = γcirc⌝ ∗
                 "Hinit" ∷ wal_init_ghost_state γnew.
Proof.
  (* this pos is a nat *)
  iMod (ghost_var_alloc 0%nat) as (installer_pos_name) "Hinstalled_pos".
  iMod (ghost_var_alloc 0%nat) as (installer_txn_id_name) "Hinstalled_txn_id".

  iMod (ghost_var_alloc (W64 0)) as (installer_pos_mem_name) "?".
  iMod (ghost_var_alloc 0%nat) as (installer_txn_id_mem_name) "?".

  iMod (ghost_var_alloc (W64 0)) as (logger_pos_name) "?".
  iMod (ghost_var_alloc 0%nat) as (logger_txn_id_name) "?".

  iMod (ghost_var_alloc (W64 0)) as (installed_pos_mem_name) "?".
  iMod (ghost_var_alloc 0%nat) as (installed_txn_id_mem_name) "?".

  iMod (mono_nat_own_alloc 0%nat) as (diskEnd_mem_name) "[? _]".
  iMod (mono_nat_own_alloc 0%nat) as (diskEnd_mem_txn_id_name) "[? _]".

  iMod (ghost_var_alloc 0%nat) as (diskEnd_name) "?".
  iMod (ghost_var_alloc 0%nat) as (diskEnd_txn_id_name) "?".

  iMod (ghost_var_alloc ([] : list update.t)) as (already_installed_name) "Halready_installed".
  iMod (mono_nat_own_alloc 0%nat) as (being_installed_start_txn_name) "[Hbeing_start _]".
  iMod (map_init (K:=nat) (V:=unit) ∅) as (γstable_txn_ids_name) "Hstable_txns".
  iMod (alist_alloc (@nil (u64 * list update.t))) as (γtxns_ctx_name) "Htxns_ctx".
  iMod (thread_own_alloc True with "[//]") as (start_avail_name) "(Hstart_avail_ctx&Hstart_avail)".
  iMod (thread_own_alloc True with "[//]") as (diskEnd_avail_name) "(HdiskEnd_avail_ctx&HdiskEnd_avail)".
  iMod (ghost_var_alloc (inhabitant : circΣ.t)) as (cs_name) "Hcs".
  iMod (ghost_var_alloc ([] : list (u64 * list update.t))) as (txns_name) "Htxns".

  iModIntro.
  iExists {| circ_name := γcirc;
            cs_name := cs_name;
            txns_ctx_name := γtxns_ctx_name;
            txns_name := txns_name;
            being_installed_start_txn_name := being_installed_start_txn_name;
            already_installed_name := already_installed_name;
            diskEnd_avail_name := diskEnd_avail_name;
            start_avail_name := start_avail_name;
            stable_txn_ids_name := γstable_txn_ids_name;
            logger_pos_name := logger_pos_name;
            logger_txn_id_name := logger_txn_id_name;
            installer_pos_mem_name := installer_pos_mem_name;
            installer_txn_id_mem_name := installer_txn_id_mem_name;
            installer_pos_name := installer_pos_name;
            installer_txn_id_name := installer_txn_id_name;
            diskEnd_mem_name := diskEnd_mem_name;
            diskEnd_mem_txn_id_name := diskEnd_mem_txn_id_name;
            diskEnd_name := diskEnd_name;
            diskEnd_txn_id_name := diskEnd_txn_id_name;
            installed_pos_mem_name := installed_pos_mem_name;
            installed_txn_id_mem_name := installed_txn_id_mem_name;
            base_disk_name := γ.(base_disk_name) |}; simpl.
  by iFrame.
Qed.

Definition log_state0 bs : log_state.t :=
  {|
    log_state.d := list_to_map (imap (λ (i : nat) (x : Block), (513 + i, x)) bs);
    log_state.txns := [(W64 0, [])];
    log_state.installed_lb := 0;
    log_state.durable_lb := 0
  |}.

Lemma alloc_wal_init_ghost_state' γcirc bs :
  ⊢ |==> ∃ γbasedisk γnew,
      "#Hbase_disk" ∷ is_base_disk γnew (log_state0 bs).(log_state.d) ∗
      "%Hbase_name" ∷ ⌜γnew.(base_disk_name) = γbasedisk⌝ ∗
      "%Hcirc_name" ∷ ⌜γnew.(circ_name) = γcirc⌝ ∗
      "Hinit" ∷ wal_init_ghost_state γnew.
Proof.
  iMod (own_alloc (to_agree (log_state0 bs).(log_state.d))) as (γbasedisk) "H".
  { done. }
  iMod (alloc_wal_init_ghost_state (wal_names_dummy <| base_disk_name := γbasedisk |>) γcirc) as (γnew Heq1 Heq2) "?"; iNamed.
  simpl in Heq1; subst.
  rewrite /is_base_disk.
  iModIntro.
  iExists _, _; iFrame.
  eauto.
Qed.

Lemma log_state0_wf bs : wal_wf (log_state0 bs).
Proof.
  rewrite /wal_wf /=.
  split_and!; try lia.
  - change (log_state.updates (log_state0 bs)) with (@nil update.t).
    rewrite /addrs_wf.
    apply Forall_nil; auto.
  - rewrite /list_mono; intros.
    apply lookup_lt_Some in Hx1.
    apply lookup_lt_Some in Hx2.
    simpl in Hx1, Hx2.
    lia.
Qed.

Lemma log_state0_post_crash bs : wal_post_crash (log_state0 bs).
Proof.
  rewrite /wal_post_crash /=.
  auto.
Qed.

Definition logger_resources γ : iProp Σ :=
  (* subset of logger, with the pre resources needed to eventually form [is_circular_appender], which depends on in-memory state *)
  ∃ diskEnd diskEnd_txn_id,
    "HnotLogging" ∷ thread_own γ.(diskEnd_avail_name) Available ∗
    "HownLoggerPos_logger" ∷ ghost_var γ.(logger_pos_name) (1/2) diskEnd ∗
    "HownLoggerTxn_logger" ∷ ghost_var γ.(logger_txn_id_name) (1/2) diskEnd_txn_id ∗
    "HownDiskEndMem_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2) (uint.nat diskEnd) ∗
    "HownDiskEndMemTxn_logger" ∷ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2) diskEnd_txn_id ∗
    "HownDiskEnd_logger" ∷ ghost_var γ.(diskEnd_name) (1/2) (uint.nat diskEnd) ∗
    "HownDiskEndTxn_logger" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/2) diskEnd_txn_id ∗
    "Happender_pre" ∷ is_circular_appender_pre γ.(circ_name).

Definition wal_resources γ : iProp Σ :=
  logger_resources γ ∗ installer_inv γ.

Definition background_inv l γ : iProp Σ :=
  ∃ (circ_l: loc),
    l ↦[Walog :: "circ"] #circ_l ∗
    logger_inv γ circ_l ∗
    installer_inv γ.

Ltac iDestruct_2 H :=
  (* TODO(tej): I'm sorry *)
  let pat := eval cbv in ("[" +:+ H +:+ " " +:+ H +:+ "2]") in
  iDestruct H as pat.

Definition memLog_linv_init_ghost_state γ : iProp Σ :=
  (ghost_var γ.(txns_name) (1/2) [(W64 0, [])]
    ∗ ghost_var γ.(logger_pos_name) (1/2) (W64 0)
    ∗ ghost_var γ.(logger_txn_id_name) (1/2) 0%nat
    ∗ ghost_var γ.(installer_pos_mem_name) (1/2) (W64 0)
    ∗ ghost_var γ.(installer_txn_id_mem_name) (1/2) 0%nat
    ∗ mono_nat_auth_own γ.(diskEnd_mem_name) (1/2/2) 0%nat
    ∗ mono_nat_auth_own γ.(diskEnd_mem_txn_id_name) (1/2/2) 0%nat
    ∗ ghost_var γ.(installed_pos_mem_name) (1/2) (W64 0)
    ∗ ghost_var γ.(installed_txn_id_mem_name) (1/2) 0%nat
    ∗ map_ctx γ.(stable_txn_ids_name) (1/2) {[0%nat := ()]}).

Definition memLog_linv_init_pers_state γ : iProp Σ :=
  (0%nat [[γ.(stable_txn_ids_name)]]↦ro () ∗
  txn_pos γ 0 0 ∗
  mono_nat_lb_own γ.(being_installed_start_txn_name) 0).

Lemma memLog_linv_pers_core_init γ :
  memLog_linv_init_pers_state γ
  -∗ memLog_linv_pers_core γ
    {| slidingM.log := []; slidingM.start := 0; slidingM.mutable := 0 |} 0 0 0 0
    [(W64 0, [])] 0 0 0 0.
Proof.
  iIntros "#(?&?&?)".
  rewrite /memLog_linv_pers_core /named /=.
  change (slidingM.endPos _) with (W64 0).
  rewrite /slidingM.memEnd /=.
  iFrame "#".
  iSplit; first by done.
  iSplit; first by done.
  iSplit; first by done.
  rewrite /memLog_linv_txns /named /slidingM.logIndex /mwrb.logend /=.
  replace (uint.nat 0) with 0%nat by word.
  simpl.
  iPureIntro.
  split.
  2: {
    split; last by word.
    apply Forall_forall.
    intros x Hx.
    apply list_elem_of_singleton in Hx.
    subst x.
    word.
  }
  replace (_ :: _) with (replicate 6 {| mwrb.txn := 1; mwrb.upd := 0 |});
    last by reflexivity.
  split.
  {
    intros bndry Hbndry.
    apply elem_of_replicate_inv in Hbndry.
    subst bndry.
    intuition.
  }
  intros i bndry1 bndry2 Hbndry1 Hbndry2.
  apply list_elem_of_lookup_2 in Hbndry1.
  apply list_elem_of_lookup_2 in Hbndry2.
  apply elem_of_replicate_inv in Hbndry1.
  apply elem_of_replicate_inv in Hbndry2.
  subst bndry1 bndry2.
  split; first by reflexivity.
  split; first by reflexivity.
  split; first by apply has_updates_nil.
  simpl.
  intros upd Hin.
  rewrite subslice_zero_length in Hin.
  inversion Hin.
Qed.

Lemma memLog_linv_nextDiskEnd_txn_id_init γ :
  memLog_linv_init_pers_state γ -∗
  map_ctx γ.(stable_txn_ids_name) (1/2) {[0%nat := ()]} -∗
    memLog_linv_nextDiskEnd_txn_id γ 0 0.
Proof.
  iIntros "#(?&?&?) Hstable".
  iExists ({[0%nat:=()]} : gmap nat unit).
  iFrame "∗ #".
  iPureIntro.
  intros txn_id Hlb.
  apply lookup_singleton_ne.
  lia.
Qed.

Lemma memLog_linv_init γ :
  memLog_linv_init_pers_state γ -∗
  memLog_linv_init_ghost_state γ -∗
    memLog_linv γ
      {| slidingM.log := [];
         slidingM.start := 0;
         slidingM.mutable := 0; |} 0 0.
Proof.
  iIntros "#Hpers Hvars".
  iDestruct "Hvars" as "(?&?&?&?&?&?&?&?&?&Hstable)".
  rewrite /memLog_linv.
  iExists 0%nat, 0%nat, [(W64 0, [])], (W64 0), 0%nat, (W64 0), 0%nat.
  rewrite /memLog_linv_core /named.
  iDestruct (memLog_linv_pers_core_init with "Hpers") as "$".
  simpl.
  iDestruct (memLog_linv_nextDiskEnd_txn_id_init with "Hpers Hstable") as "$".
  iFrame.
Qed.

Lemma wal_linv_durable_init γ :
  (diskEnd_at_least γ.(circ_name) 0
   ∗ thread_own_ctx γ.(diskEnd_avail_name)
       (diskEnd_is γ.(circ_name) (1 / 2) 0))
  ∗ (start_at_least γ.(circ_name) 0
     ∗ thread_own_ctx γ.(start_avail_name) (start_is γ.(circ_name) (1 / 2) 0)) -∗
  memLog_linv_init_pers_state γ -∗
  memLog_linv_init_ghost_state γ -∗
  wal_linv_durable γ {| circΣ.upds := []; circΣ.start := W64 0; |}.
Proof.
  iIntros "[[#HdiskEnd_lb HdiskEnd_ctx] [#Hstart_lb Hstart_ctx]] #HmemLog_pers HmemLog_ghost".
  rewrite /wal_linv_durable.
  iExists {| diskEnd := W64 0;
             locked_diskEnd_txn_id := 0;
             memLog := _;
          |}; simpl.
  change (circΣ.diskEnd _) with 0.
  iSplit; first by done.
  iSplit; first by done.
  rewrite /locked_wf /diskEnd_linv /diskStart_linv /=.
  iSplit.
  { iPureIntro.
    split; [ done | ].
    rewrite /slidingM.wf /=.
    word. }
  rewrite /named.
  iFrame "∗#".
  iApply (memLog_linv_init with "HmemLog_pers HmemLog_ghost").
Qed.

Lemma disk_array_to_big_opM_ind arrEnd bs :
  (arrEnd - length bs) d↦∗ bs -∗
  [∗ map] a↦b ∈ list_to_map (imap (λ i b', (arrEnd - length bs + i, b')) bs), a d↦ b.
Proof.
  iInduction bs as [|b0] "IH"; first by eauto.
  iIntros "Hbs".
  rewrite disk_array_cons /= Z.add_0_r.
  iDestruct "Hbs" as "[Hb0 Hbs]".
  replace (arrEnd - S (length bs) + 1) with (arrEnd - length bs) by lia.
  iApply "IH" in "Hbs".
  iApply (big_sepM_insert_2 with "[Hb0]").
  1: eauto.
  replace (imap ((λ (i : nat) (b' : Block), (arrEnd - S (length bs) + i, b')) ∘ S) bs)
    with (imap (λ (i : nat) (b' : Block), (arrEnd - length bs + i, b')) bs).
  1: iAssumption.
  apply imap_ext.
  intros a b Hin.
  simpl.
  f_equal.
  lia.
Qed.

Lemma disk_array_to_big_opM start bs :
  start d↦∗ bs -∗
  [∗ map] a↦b ∈ list_to_map (imap (λ i b', (start + i, b')) bs), a d↦ b.
Proof.
  replace start with ((start + length bs) - length bs) by lia.
  apply disk_array_to_big_opM_ind.
Qed.

Lemma dom_blocks_to_map_u64 {A} (f: Block → A) (bs: list Block) :
  dom (list_to_map (imap (λ i x, (W64 (513 + i), f x)) bs) : gmap u64 _) =
  rangeSet 513 (length bs).
Proof.
  rewrite dom_list_to_map_L.
  rewrite fmap_imap /=.
  change (λ n, fst ∘ _) with (λ (n:nat) (_:Block), W64 (513 + n)).
  rewrite /rangeSet.
  f_equal.
  remember 513 as start. clear Heqstart.
  generalize dependent start.
  induction bs; simpl; intros.
  - reflexivity.
  - rewrite -> seqZ_cons by lia.
    replace (Z.succ start) with (start + 1)%Z by lia.
    replace (Z.pred (S (length bs))) with (Z.of_nat $ length bs) by lia.
    rewrite fmap_cons.
    replace (start + 0%nat) with start by lia.
    f_equal.
    rewrite -IHbs.
    apply imap_ext; intros; simpl.
    f_equal.
    lia.
Qed.

Lemma dom_blocks_to_map_Z {A} (f: Block → A) (bs: list Block) :
  dom (list_to_map (imap (λ i x, (513 + i, f x)) bs) : gmap Z _) =
  list_to_set (seqZ 513 (length bs)).
Proof.
  rewrite dom_list_to_map_L.
  rewrite fmap_imap /=.
  change (λ n, fst ∘ _) with (λ (n:nat) (_:Block), (513 + n)).
  f_equal.
  remember 513 as start. clear Heqstart.
  generalize dependent start.
  induction bs; simpl; intros.
  - reflexivity.
  - rewrite -> seqZ_cons by lia.
    replace (Z.succ start) with (start + 1) by lia.
    replace (Z.pred (S (length bs))) with (Z.of_nat $ length bs) by lia.
    replace (start + 0%nat) with start by lia.
    f_equal.
    rewrite -IHbs.
    apply imap_ext; intros; simpl.
    lia.
Qed.

Lemma is_wal_inner_durable_init (bs: list Block) :
  dom dinit = list_to_set (seqZ 513 (length bs)) →
  0 d↦∗ repeat block0 513 ∗
  513 d↦∗ bs ==∗
  let σ := log_state0 bs in
  ∃ γ, is_wal_inner_durable γ σ dinit ∗ wal_resources γ.
Proof.
  iIntros (Hdinit_dom) "[Hlog Hdata]".
  iMod (circular_init with "Hlog") as (γcirc) "(Hcirc & Hcirc_appender & Hstart & Hend)".
  iDestruct (start_is_to_at_least with "Hstart") as "#Hstart_lb".
  iDestruct (diskEnd_is_to_at_least with "Hend") as "#Hend_lb".
  iMod (alloc_wal_init_ghost_state' γcirc bs) as (γbasedisk γ) "Hinit". iNamed "Hinit".

  iNamed "Hinit".
  iMod (map_alloc_ro 0%nat () with "stable_txn_ids") as "[stable_txn_ids #H0stable]".
  { done. }
  change (<[0%nat:=()]> ∅) with ({[0%nat:=()]} : gmap nat unit).
  iMod (ghost_var_update [(W64 0, [])] with "txns") as "txns".
  iMod (ghost_var_update {| circΣ.upds := []; circΣ.start := W64 0 |} with "cs") as "cs".
  iDestruct_2 "logger_pos".
  iDestruct_2 "logger_txn_id".
  iDestruct_2 "installer_pos".
  iDestruct_2 "installer_txn_id".
  iDestruct_2 "txns".
  iDestruct_2 "stable_txn_ids".
  iDestruct_2 "diskEnd_mem".
  iDestruct_2 "diskEnd_mem_txn_id".
  iDestruct_2 "diskEnd".
  iDestruct_2 "diskEnd_txn_id".
  iDestruct_2 "installed_pos_mem".
  iDestruct_2 "installed_txn_id_mem".
  iDestruct_2 "installer_pos_mem".
  iDestruct_2 "installer_txn_id_mem".
  iDestruct_2 "already_installed".
  iDestruct_2 "being_installed_start_txn".
  iDestruct "diskEnd_mem" as "[diskEnd_mem11 diskEnd_mem12]".
  iDestruct "diskEnd_mem_txn_id"
    as "[diskEnd_mem_txn_id11 diskEnd_mem_txn_id12]".

  iDestruct (mono_nat_lb_own_get with "being_installed_start_txn")
    as "#being_installed_start_txn_lb".
  iDestruct (mono_nat_lb_own_get with "diskEnd_mem_txn_id2")
    as "#diskEnd_mem_txn_id_lb".
  iMod (alloc_txn_pos (W64 0) [] with "txns_ctx") as "[txns_ctx _]".
  simpl.
  iMod (thread_own_replace with "start_avail_ctx start_avail Hstart")
    as "(start_avail_ctx&start_avail)".
  iMod (thread_own_replace with "diskEnd_avail_ctx diskEnd_avail Hend")
    as "(diskEnd_avail_ctx&diskEnd_avail)".

  subst.
  iModIntro.
  iExists γ.
  rewrite /is_wal_inner_durable.
  cbn [log_state.txns log_state0].
  iPoseProof (txns_ctx_txn_pos _ _ 0 0 with "txns_ctx") as "#Htxn_pos".
  1: rewrite //.
  iFrame "txns_ctx txns".
  iAssert (memLog_linv_init_ghost_state _) with "[$]" as "HmemLog_ghost".
  iAssert (is_installed_core_ghost _ _ _) with "[$]" as "Hinstalled_ghost".

  iSplitL "Hcirc stable_txn_ids cs
    HmemLog_ghost start_avail_ctx diskEnd_avail_ctx
    Hinstalled_ghost Hdata
    installer_pos2 installer_txn_id2
    diskEnd_mem11 diskEnd_mem_txn_id11
    diskEnd2 diskEnd_txn_id2
  ".
  2: {
    iFrame.
    replace (uint.nat 0) with 0%nat by word. iFrame "∗#".
  }
  iSplit; first by eauto using log_state0_wf.
  iSplit; first by eauto using log_state0_post_crash.
  rewrite /nextDiskEnd_inv.
  iSplitL "stable_txn_ids".
  {
    iExists _; iFrame.
    rewrite big_sepM_singleton. iFrame "#".
    iPureIntro.
    rewrite /stable_sound.
    intros.
    rewrite /is_txn in H1, H2.
    rewrite -list_lookup_fmap /= in H1.
    rewrite -list_lookup_fmap /= in H2.
    apply lookup_lt_Some in H1.
    apply lookup_lt_Some in H2.
    simpl in *; lia.
  }
  iExists _; iFrame.
  iSplitL "HmemLog_ghost start_avail_ctx diskEnd_avail_ctx".
  {
    iApply (wal_linv_durable_init with "[start_avail_ctx diskEnd_avail_ctx] [] HmemLog_ghost").
    all: iFrame "∗#".
  }
  iSplitL "Hdata".
  {
    iSplit; first by (rewrite /log_state0 /=; iPureIntro; lia).
    iSplit; first by (rewrite subslice_zero_length; iApply txns_are_nil).
    iApply (big_sepM_mono (λ a b, a d↦ b)%I).
    {
      iIntros (addr b Hb) "?".
      iExists _, 0%nat.
      iFrame.
      iPureIntro.
      split.
      2: {
        apply elem_of_list_to_map_2 in Hb.
        destruct (elem_of_lookup_imap_1 _ _ _ Hb) as (a'&b'&Ha'&Hlookup).
        inversion Ha'.
        rewrite /LogSz.
        lia.
      }
      split; first by lia.
      intuition.
    }
    iApply (disk_array_to_big_opM with "Hdata").
  }
  iSplitL.
  {
    iFrame.
    iPureIntro.
    split; last by (simpl; word).
    split.
    {
      simpl.
      intros bndry Hbndry.
      do 4 (
        apply elem_of_cons in Hbndry;
        destruct Hbndry as [->|Hbndry];
        first by (simpl; word)
      ).
      inversion Hbndry.
    }
    simpl.
    intros i bndry1 bndry2 Hbndry1 Hbndry2.
    assert (
      bndry1 = {| mwrb.txn := 1%nat; mwrb.upd := 0%nat |} ∧
      bndry2 = {| mwrb.txn := 1%nat; mwrb.upd := 0%nat |}
    ) as [-> ->].
    {
      do 4 (destruct i; first by (
        simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
        simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2;
        intuition
      )).
      inversion Hbndry1.
    }
    simpl.
    split; first by lia.
    split; first by lia.
    rewrite subslice_nil subslice_zero_length.
    apply is_memLog_region_nil.
  }
  iFrame "#".
  iSplit; first by rewrite /log_state0 //.
  iPureIntro.
  split.
  {
    exists (W64 0), 0%nat.
    rewrite /log_state0 /circΣ.diskEnd /=.
    split; first by lia.
    split; first by lia.
    split; first by apply Forall_nil_2.
    split; first by constructor.
    split; first by word.
    constructor.
  }
  intros.
  rewrite -!elem_of_dom.
  rewrite Hdinit_dom.
  f_equiv.
  simpl.
  rewrite dom_blocks_to_map_Z //.
Qed.

Lemma is_base_disk_crash γ γ' d :
  γ'.(base_disk_name) = γ.(base_disk_name) →
  is_base_disk γ d ⊢@{_} is_base_disk γ' d.
Proof.
  rewrite /is_base_disk => -> //.
Qed.

Definition map_set_ctx {K} `{Countable K} `{!mapG Σ K ()}
           (γ: gname) q (m: gmap K ()) : iProp Σ :=
  map_ctx γ q m ∗
  [∗ map] k↦_ ∈ m, ptsto_ro γ k ().

Lemma map_set_ctx_alloc1 {K} `{Countable K} `{!mapG Σ K ()} {γ: gname} (k:K) (s: gset K) :
  map_set_ctx γ 1 (gset_to_gmap () s) -∗
  |==> map_set_ctx γ 1 (gset_to_gmap () ({[k]} ∪ s)) ∗
       ptsto_ro γ k ().
Proof.
  iDestruct 1 as "[Hctx Hro]".
  destruct (gset_to_gmap () s !! k) eqn:Hlookup.
  - (* already there, just need to extract it *)
    iModIntro.
    destruct u.
    iDestruct (big_sepM_lookup _ _ k () with "Hro") as "#$"; first by auto.
    replace ({[k]} ∪ s) with s; [ by iFrame | ].
    apply lookup_gset_to_gmap_Some in Hlookup as [? _].
    set_solver.
  - iMod (map_alloc_ro k () with "Hctx") as "[Hctx #Hk]"; first by auto.
    iModIntro.
    iFrame "Hk".
    rewrite gset_to_gmap_union_singleton.
    iFrame.
    rewrite big_sepM_insert //.
    iFrame "∗#".
Qed.

Lemma map_set_ctx_alloc {K} `{Countable K} `{!mapG Σ K ()} {γ: gname} (s' s: gset K) :
  map_set_ctx γ 1 (gset_to_gmap () s) -∗
  |==> map_set_ctx γ 1 (gset_to_gmap () (s' ∪ s)) ∗
       [∗ set] k ∈ s', ptsto_ro γ k ().
Proof.
  iIntros "Hctx".
  iInduction s' as [|k s'] "IH" using set_ind_L.
  - rewrite left_id_L big_sepS_empty.
    by iFrame.
  - rewrite -union_assoc_L.
    rewrite gset_to_gmap_union_singleton.
    rewrite big_sepS_insert //.
    iMod ("IH" with "Hctx") as "[Hctx $]".
    iMod (map_set_ctx_alloc1 k with "Hctx") as "[Hctx #$]".
    iModIntro.
    rewrite gset_to_gmap_union_singleton //.
Qed.

Lemma map_alloc_ro_set {K} `{Countable K} `{!mapG Σ K ()} {γ: gname} (s: gset K) :
  map_ctx γ 1 (∅ : gmap K ()) -∗
  |==> map_ctx γ 1 (gset_to_gmap () s) ∗
       [∗ set] k∈s, ptsto_ro γ k ().
Proof.
  iIntros "Hctx".
  iMod (map_set_ctx_alloc s ∅ with "[Hctx]") as "[Hctx $]".
  - rewrite /map_set_ctx.
    rewrite gset_to_gmap_empty.
    rewrite big_sepM_empty.
    iFrame.
  - rewrite right_id_L.
    iDestruct "Hctx" as "[$ _]".
    auto.
Qed.

Lemma init_stable_txns γstable_txn_ids_name (installed_txn_id diskEnd_txn_id durable_lb : nat) :
  map_ctx   γstable_txn_ids_name 1 (∅ : gmap nat unit) -∗
  |==> "Hstable_txns" ∷ map_ctx γstable_txn_ids_name 1 (gset_to_gmap () {[diskEnd_txn_id; installed_txn_id; (durable_lb `max` diskEnd_txn_id)%nat]}) ∗
       "#HdiskEnd_stable" ∷ diskEnd_txn_id [[γstable_txn_ids_name]]↦ro () ∗
       "#Hnew_durable_lb_stable" ∷
          (durable_lb `max` diskEnd_txn_id)%nat [[γstable_txn_ids_name]]↦ro () ∗
       "#Hinstalled_txn_id_stable" ∷ installed_txn_id [[γstable_txn_ids_name]]↦ro () ∗
       "#Hstable_ro" ∷ ([∗ map] txn_id ↦ _ ∈ (gset_to_gmap () {[diskEnd_txn_id; installed_txn_id; (durable_lb `max` diskEnd_txn_id)%nat]}),
                       txn_id [[γstable_txn_ids_name]]↦ro tt).
Proof.
  iIntros "Hstable_txns".
  iMod (map_alloc_ro_set with "Hstable_txns") as "[$ Hro]".
  iModIntro.

  iDestruct (big_sepS_elem_of with "Hro") as "#$"; first by set_solver.
  iDestruct (big_sepS_elem_of with "Hro") as "#$"; first by set_solver.
  iDestruct (big_sepS_elem_of with "Hro") as "#$"; first by set_solver.
  iApply big_sepM_dom.
  rewrite dom_gset_to_gmap.
  eauto.
Qed.

Lemma is_installed_txn_crash γ γ' cs txns installed_txn_id installed_lb crash_txn  :
  (installed_txn_id ≤ crash_txn)%nat →
  is_installed_txn γ cs txns installed_txn_id installed_lb -∗
  installed_txn_id [[γ'.(stable_txn_ids_name)]]↦ro () -∗
  is_installed_txn γ' cs (take (S crash_txn) txns) installed_txn_id installed_lb.
Proof.
  iIntros (?). iNamed 1. iIntros "#Hstart_stable'".
  rewrite /is_installed_txn.
  iFrame "%#".
  iPureIntro.
  rewrite /is_txn in Hstart_txn |- *.
  rewrite -> lookup_take_lt by lia.
  auto.
Qed.

Lemma is_durable_txn_crash γ γ' cs txns diskEnd_txn_id durable_lb :
  is_durable_txn γ cs txns diskEnd_txn_id durable_lb -∗
  diskEnd_txn_id [[γ'.(stable_txn_ids_name)]]↦ro () -∗
  (durable_lb `max` diskEnd_txn_id)%nat [[γ'.(stable_txn_ids_name)]]↦ro () -∗
  let new_durable_lb := (durable_lb `max` diskEnd_txn_id)%nat in
  is_durable_txn γ'
    cs (take (S new_durable_lb) txns) diskEnd_txn_id new_durable_lb.
Proof.
  iNamed 1. iIntros "#Hend_txn_stable' #Hdurable_lb_stable'".
  rewrite /is_durable_txn length_take.
  rewrite (Nat.max_l (_ `max` _) _); last by lia.
  iExists diskEnd, diskEnd_txn_id; iFrame "%#".
  iPureIntro.
  pose proof (is_txn_bound _ _ _ Hend_txn).
  split; first by lia.
  rewrite subslice_to_end; last by (rewrite length_take; lia).
  rewrite -subslice_take_drop.
  split; first by lia.
  split.
  {
    destruct (decide (durable_lb ≤ diskEnd_txn_id)%nat).
    {
      rewrite Nat.max_r; last by lia.
      rewrite subslice_zero_length.
      apply Forall_nil_2.
    }
    rewrite Nat.max_l; last by lia.
    rewrite -(subslice_app_contig _ (S diskEnd_txn_id)) in Hdurable_nils;
      last by lia.
    apply Forall_app in Hdurable_nils.
    intuition.
  }
  split.
  {
    apply is_txn_take.
    assumption.
  }
  destruct (decide (durable_lb ≤ diskEnd_txn_id)%nat)
    as [Hcmp|Hcmp].
  {
    rewrite Nat.max_r; last by lia.
    apply is_txn_take; assumption.
  }
  rewrite Nat.max_l; last by lia.
  apply (is_txn_from_take_is_txn (S diskEnd_txn_id)).
  rewrite take_take.
  rewrite Nat.min_l; last by lia.
  apply is_txn_take.
  assumption.
Qed.

Lemma diskEnd_linv_post_crash γ' diskEnd Q :
  uint.Z (W64 diskEnd) = diskEnd →
  diskEnd_is γ'.(circ_name) (1/2) diskEnd -∗
  thread_own_ctx γ'.(diskEnd_avail_name) Q -∗
  thread_own γ'.(diskEnd_avail_name) Available -∗
  |==> diskEnd_linv γ' diskEnd ∗
        thread_own γ'.(diskEnd_avail_name) Available.
Proof.
  iIntros (Hbound) "H Hctx Havail".
  iDestruct (diskEnd_is_to_at_least with "[$]") as "#Hatleast".
  iMod (thread_own_get with "Hctx Havail") as "(Hctx & _ & Hused)".
  rewrite /diskEnd_linv.
  replace (uint.Z (W64 diskEnd)) with diskEnd by auto.
  iMod (thread_own_put (diskEnd_is γ'.(circ_name) (1/2) diskEnd) with
        "Hctx Hused H") as "[$ $]".
  by iFrame "#".
Qed.

Lemma diskStart_linv_post_crash γ' start Q :
  start_is γ'.(circ_name) (1/2) start -∗
  thread_own_ctx γ'.(start_avail_name) Q -∗
  thread_own γ'.(start_avail_name) Available -∗
  |==> diskStart_linv γ' start ∗
       thread_own γ'.(start_avail_name) Available.
Proof.
  iIntros "H Hctx Havail".
  iDestruct (start_is_to_at_least with "[$]") as "#Hatleast".
  iMod (thread_own_get with "Hctx Havail") as "(Hctx & _ & Hused)".
  rewrite /diskEnd_linv.
  iMod (thread_own_put (start_is γ'.(circ_name) (1/2) start) with
        "Hctx Hused H") as "[$ $]".
  by iFrame "#".
Qed.

Lemma memLog_linv_nextDiskEnd_txn_id_post_crash γ diskEnd diskEnd_txn_id installed_txn_id durable_lb :
  (installed_txn_id ≤ diskEnd_txn_id)%nat →
  map_ctx γ.(stable_txn_ids_name) (1/2) (gset_to_gmap () {[diskEnd_txn_id; installed_txn_id; (durable_lb `max` diskEnd_txn_id)%nat]}) -∗
  txn_pos γ (durable_lb `max` diskEnd_txn_id) diskEnd -∗
  (durable_lb `max` diskEnd_txn_id)%nat [[γ.(stable_txn_ids_name)]]↦ro () -∗
  memLog_linv_nextDiskEnd_txn_id γ diskEnd (durable_lb `max` diskEnd_txn_id)%nat.
Proof.
  iIntros (Hbound) "Hctx #Hpos #HdiskEnd_stable".
  iExists _; iFrame "∗#".
  iPureIntro.
  intros ??.
  apply lookup_gset_to_gmap_None.
  assert (txn_id ≠ diskEnd_txn_id) by lia.
  assert (txn_id ≠ installed_txn_id) by lia.
  assert (txn_id ≠ (durable_lb `max` diskEnd_txn_id)%nat) by lia.
  set_solver.
Qed.

Lemma is_durable_txn_get_txn_pos γ' cs txns diskEnd_txn_id durable_lb :
  is_durable_txn γ' cs txns diskEnd_txn_id durable_lb -∗
  txns_ctx γ' txns -∗
  txn_pos γ' diskEnd_txn_id (W64 (circΣ.diskEnd cs)) ∗
  txn_pos γ' (durable_lb `max` diskEnd_txn_id) (W64 (circΣ.diskEnd cs)).
Proof.
  iNamed 1.
  iIntros "Hctx".
  iSplit.
  {
    iDestruct (txns_ctx_txn_pos with "Hctx") as "$"; eauto.
    replace (W64 (circΣ.diskEnd cs)) with diskEnd by word; auto.
  }
  iDestruct (txns_ctx_txn_pos with "Hctx") as "$"; eauto.
  replace (W64 (circΣ.diskEnd cs)) with diskEnd by word; auto.
Qed.

Lemma txns_mono_lt_last σ diskEnd :
  wal_wf σ →
  is_txn σ.(log_state.txns) (length σ.(log_state.txns) - 1) diskEnd →
  Forall (λ pos, uint.Z pos ≤ uint.Z diskEnd) σ.(log_state.txns).*1.
Proof.
  intros Hwf Htxn.
  apply Forall_forall => pos Hin.
  apply list_elem_of_lookup in Hin as [txn_id Hlookup].
  assert (is_txn σ.(log_state.txns) txn_id pos).
  { rewrite /is_txn.
    rewrite -list_lookup_fmap //. }
  eapply (wal_wf_txns_mono_pos' (txn_id1:=txn_id)); eauto.
  apply is_txn_bound in H.
  lia.
Qed.

Lemma stable_sound_crash txns stable_txns crash_txn :
  stable_sound txns stable_txns →
  stable_sound (take crash_txn txns) stable_txns.
Proof.
  rewrite /stable_sound;
    intros Hstable ??? Hgt Hlookup Htxn Htxn'.
  specialize (Hstable _ _ pos Hgt Hlookup).
  rewrite /is_txn in Htxn; fmap_Some in Htxn as txn.
  rewrite /is_txn in Htxn'; fmap_Some in Htxn' as txn'.
  pose proof (lookup_take_Some _ _ _ _ Htxn).
  pose proof (lookup_take_Some _ _ _ _ Htxn').
  rewrite lookup_take_lt in Htxn; auto.
  rewrite lookup_take_lt in Htxn'; auto.
  rewrite lookup_take_lt //.
  apply Hstable; rewrite /is_txn.
  - rewrite Htxn //.
  - rewrite Htxn' /=.
    congruence.
Qed.

Lemma nextDiskEnd_inv_post_crash_stable_sound γ txns installed_txn_id diskEnd_txn_id durable_lb :
  Forall (λ x, snd x = nil) (subslice (S diskEnd_txn_id) (S (durable_lb `max` diskEnd_txn_id)) txns) →
  nextDiskEnd_inv γ txns -∗
  installed_txn_id [[γ.(stable_txn_ids_name)]]↦ro () -∗
  ⌜let stable_txns' := gset_to_gmap tt {[diskEnd_txn_id; installed_txn_id; (durable_lb `max` diskEnd_txn_id)%nat]} in
  stable_sound (take (S (durable_lb `max` diskEnd_txn_id))%nat txns) stable_txns'⌝.
Proof.
  intros Hnils.
  simpl.
  iNamed 1. iIntros "Hinstalled_stable".
  iDestruct (map_ro_valid with "Hstablectx Hinstalled_stable") as %Hinstalled_stable.
  apply (stable_sound_crash _ _ (S (durable_lb `max` diskEnd_txn_id))) in HafterNextDiskEnd.
  iPureIntro.

  iIntros (??? Hlt Hlookup Htxn Htxn').
  apply lookup_gset_to_gmap_Some in Hlookup as [Hlookup _].
  pose proof Htxn' as Htxn'_backup.
  rewrite /is_txn in Htxn'.
  fmap_Some in Htxn' as txn'.
  assert (Htxn'_lt:=Htxn').
  apply mk_is_Some, lookup_lt_is_Some_1 in Htxn'_lt.
  rewrite length_take in Htxn'_lt.
  assert (txn_id = diskEnd_txn_id ∨ txn_id = installed_txn_id ∨ txn_id = (durable_lb `max` diskEnd_txn_id)%nat) as [-> | [-> | ->]] by set_solver.
  { (* we're talking about diskEnd_txn_id *)
    unshelve (epose proof (iffLR (Forall_forall _ _) Hnils _ _) as Hnil).
    2: {
      apply list_elem_of_lookup.
      eexists (txn_id' - (S diskEnd_txn_id))%nat.
      rewrite subslice_lookup; last by lia.
      rewrite -(lookup_take_lt _ (S (durable_lb `max` diskEnd_txn_id)));
        last by lia.
      rewrite -Nat.le_add_sub; last by lia.
      eassumption.
    }
    rewrite Htxn' /=.
    simpl in Hnil.
    rewrite Hnil.
    reflexivity.
  }
  {
    (* this is installed_txn_id, which we get from its stability before *)
    eapply HafterNextDiskEnd; eauto.
  }
  {
    move: Htxn'_lt; len.
  }
Qed.

(* Called after wpc for recovery is completed, so l is the location of the wal *)
Lemma wal_crash_obligation_alt E Prec Pcrash l γ s :
  ↑walN ⊆ E →
  is_wal_inv_pre l γ s dinit -∗
  □ (∀ s s' (Hcrash: relation.denote log_crash s s' ()),
    ▷ P s -∗ |={E ∖ ↑N.@"wal"}=> ▷ Prec s s' ∗ ▷ Pcrash s s') -∗
  ▷ P s -∗
  |={⊤}=> ∃ γ', is_wal P l γ dinit ∗
    (<bdisc> (|C={E}=> ∃ s s',
      ⌜relation.denote log_crash s s' tt⌝ ∗
      (* NOTE: need to add the ghost state that the logger will need *)
      is_wal_inner_durable γ' s' dinit ∗
      wal_resources γ' ∗ ▷ Prec s s')) ∗
      □ (|C={E}=> inv (N.@"wal") (∃ s s',
        ⌜relation.denote log_crash s s' tt⌝ ∗
        is_wal_inner_crash γ s ∗
        wal_ghost_exchange γ γ' ∗
        Pcrash s s')).
Proof.
  iIntros (Hin) "Hinv_pre #Hwand HP".
  rewrite /is_wal_inv_pre.
  iDestruct "Hinv_pre" as "(Hinner&Hcirc)".
  iDestruct "Hcirc" as (cs) "(Hcirc_state&Hcirc_pred)".

  rewrite /circular_pred.
  iMod (circ_buf_crash_obligation_alt circN (λ σ, circular_pred γ σ)%I (↑circN)
                                      (λ σ, circular_pred γ σ)%I
                                      (λ _, True)%I with "Hcirc_state [] [Hcirc_pred]") as
      (γcirc') "(#His_circular&His_circular_cfupd&His_circular_crash)".
  { solve_ndisj. }
  { iModIntro. by iIntros (σ) ">$". }
  { iFrame. }

  iMod (alloc_wal_init_ghost_state γ γcirc') as (γ') "H"; iNamed "H".
  iDestruct (own_discrete_laterable with "His_circular_cfupd") as (Pcirc_tok) "(HPcirc_tok&#HPcirc_tok_wand)".

  iExists γ'. rewrite /is_wal.
  iFrame "His_circular".
  iMod (ncinv_cinv_alloc (N.@"wal") ⊤ E
         ((∃ σ, is_wal_inner l γ σ dinit ∗ P σ) ∗
                wal_init_ghost_state γ' ∗ Pcirc_tok)
         (∃ σ σ',
               ⌜relation.denote log_crash σ σ' tt⌝ ∗
               is_wal_inner_crash γ σ ∗
               wal_ghost_exchange γ γ' ∗
               Pcrash σ σ')%I
         (∃ s s',
                 ⌜relation.denote log_crash s s' tt⌝ ∗
                 (is_wal_inner_durable γ' s' dinit) ∗ wal_resources γ' ∗ Prec s s')%I with
            "[] [Hinner HP Hinit HPcirc_tok]") as "(Hncinv&Hcfupd&Hcinv)".
  { solve_ndisj. }
  { iModIntro. iIntros "(H1&>Hinit&Htok) #HC".
    iMod ("HPcirc_tok_wand" with "[$]") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_mask_mono with "H") as (cs0') "(Hcirc&Hcirc_resources&>Hcirc_pred)"; first solve_ndisj.
    iDestruct "H1" as (σ) "(His_wal_inner&HP)".
    iDestruct "His_wal_inner" as "(>%Hwf&_&>?&>?&>?&>?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    rewrite /circular_pred.
    iDestruct (ghost_var_agree with "Howncs Hcirc_pred") as %<-.

    iDestruct (is_circular_state_wf with "[$]") as %Hcirc_wf.

    iNamed "Hinit".
    iMod (init_stable_txns γ'.(stable_txn_ids_name) installed_txn_id diskEnd_txn_id σ.(log_state.durable_lb) with "[$]") as "Hstable". iNamed "Hstable".

    set (σ':= log_crash_to
      σ (σ.(log_state.durable_lb) `max` diskEnd_txn_id)
    ).
    iDestruct (crash_to_diskEnd with "circ.end Hdurable") as %Htrans.
    iNamed "Hdurable".
    iNamed "Hinstalled". iNamed "Howninstalled".

    iMod (ghost_var_update installer_pos with "installer_pos") as "[installer_pos1 installer_pos2]".
    iMod (ghost_var_update installer_txn_id with "installer_txn_id") as "[installer_txn_id1 installer_txn_id2]".
    iMod (ghost_var_update [] with "already_installed") as "[already_installed1 already_installed2]".
    iMod (mono_nat_own_update installed_txn_id with "being_installed_start_txn") as "[[being_installed_start_txn1 being_installed_start_txn2] #being_installed_start_txn_id_mem_lb]"; first by lia.
    iMod (txns_ctx_app (take
      (S (σ.(log_state.durable_lb) `max` diskEnd_txn_id))
      σ.(log_state.txns)
    ) with "txns_ctx") as "Htxns_ctx'".
    rewrite app_nil_l.
    iMod (ghost_var_update σ'.(log_state.txns) with "txns") as "[Htxns1 Htxns2]".

    iDestruct (is_durable_txn_crash with "circ.end [$] [$]") as "#Hdurable_txn".

    iNamed "circ.end".

    replace (W64 (circΣ.diskEnd cs0)) with diskEnd by word.

    iPoseProof "circ.start" as "#circ.start2"; iNamed "circ.start2".
    iDestruct "Hcirc_resources" as "(Hcirc_start&Hcirc_diskEnd & Happender)".
    iDestruct (nextDiskEnd_inv_post_crash_stable_sound _ _ _ diskEnd_txn_id σ.(log_state.durable_lb)
                 with "HnextDiskEnd_inv Hstart_txn_stable") as %Hstable.
    {
      destruct (decide (σ.(log_state.durable_lb) ≤ diskEnd_txn_id)%nat).
      {
        rewrite Nat.max_r; last by lia.
        rewrite subslice_zero_length.
        apply Forall_nil_2.
      }
      rewrite Nat.max_l; last by lia.
      rewrite -(subslice_app_contig _ (S diskEnd_txn_id)) in Hdurable_nils;
        last by lia.
      apply Forall_app in Hdurable_nils.
      intuition.
    }

    iDestruct (txns_ctx_txn_pos _ _ installed_txn_id with "Htxns_ctx") as "#Hinstalled_pos";
      first by eauto.

    iDestruct (txns_ctx_make_factory with "Htxns_ctx Htxns_ctx'") as "[Hold_txns Htxns_ctx']".
    iDestruct (is_durable_txn_get_txn_pos with "Hdurable_txn Htxns_ctx'") as "[#HdiskEnd_pos #Hdurable_lb_pos]".
    iDestruct (txn_pos_valid_general with "Htxns_ctx' HdiskEnd_pos") as %HdiskEnd_is_txn.
    iDestruct (old_txn_get_pos with "Hold_txns Hinstalled_pos") as "#Hinstalled_pos'"; first by lia.

    iMod (diskEnd_linv_post_crash _ (uint.Z diskEnd)
            with "[Hcirc_diskEnd] diskEnd_avail_ctx diskEnd_avail")
         as "(HdiskEnd_linv & diskEnd_avail)".
    { word. }
    { iExactEq "Hcirc_diskEnd".
      auto with f_equal. }

    iMod (diskStart_linv_post_crash
         with "[Hcirc_start] start_avail_ctx start_avail")
      as "(HdiskStart_linv & start_avail)".
    { iExactEq "Hcirc_start".
      eauto with f_equal. }

    iDestruct "Hstable_txns" as "[Hstable_txns1 Hstable_txns2]".
    rewrite (Nat.max_l (_ `max` _) _); last by lia.
    iDestruct (memLog_linv_nextDiskEnd_txn_id_post_crash with
               "Hstable_txns1 Hdurable_lb_pos [$]")
              as "HnextDiskEnd_linv"; first by lia.
    iFreeze "# Hdata".

    iMod (ghost_var_update (cs0.(circΣ.start)) with "installer_pos_mem")
         as "[installer_pos_mem1 installer_pos_mem2]".
    iMod (ghost_var_update (cs0.(circΣ.start)) with "installed_pos_mem")
         as "[installed_pos_mem1 installed_pos_mem2]".
    iMod (ghost_var_update installed_txn_id with "installed_txn_id_mem")
         as "[installed_txn_id_mem1 installed_txn_id_mem2]".
    iMod (ghost_var_update installed_txn_id with "installer_txn_id_mem")
         as "[installer_txn_id_mem1 installer_txn_id_mem2]".
    iMod (ghost_var_update (W64 (circΣ.diskEnd cs0)) with "logger_pos")
        as "[logger_pos1 logger_pos2]".
    iMod (ghost_var_update diskEnd_txn_id with "logger_txn_id")
        as "[logger_txn_id1 logger_txn_id2]".
    iMod (ghost_var_update (uint.nat (circΣ.diskEnd cs0)) with "diskEnd")
        as "[diskEnd1 diskEnd2]".
    iMod (ghost_var_update diskEnd_txn_id with "diskEnd_txn_id")
        as "[diskEnd_txn_id1 diskEnd_txn_id2]".
    iMod (ghost_var_update cs0 with "cs")
        as "cs".

    iMod (mono_nat_own_update (uint.nat diskEnd) with "diskEnd_mem") as "[[[diskEnd_mem11 diskEnd_mem12] diskEnd_mem2] #diskEnd_mem_lb]"; first by lia.
    iMod (mono_nat_own_update diskEnd_txn_id with "diskEnd_mem_txn_id") as "[[[diskEnd_mem_txn_id11 diskEnd_mem_txn_id12] diskEnd_mem_txn_id2] #diskEnd_mem_txn_lb]"; first by lia.


    iThaw "Hwand".
    iMod ("Hwand" $! σ σ' with "[//] HP") as "(HPrec&HPcrash)".
    iClear "Hwand".
    iSplitL "HPcrash".
    { iModIntro. iExists σ, σ'. iFrame. iNext. eauto. }
    iExists σ, σ'. iFrame "HPrec".
    do 2iModIntro.
    iSplitL "".
    { iPureIntro. eauto. }


    iSplitR "start_avail diskEnd_avail
             being_installed_start_txn2
             installer_pos2 installer_txn_id2
             logger_pos2 logger_txn_id2
             installer_pos_mem2 installer_txn_id_mem2
             already_installed2
             installed_pos_mem2 installed_txn_id_mem2
             diskEnd2 diskEnd_txn_id2
             diskEnd_mem2 diskEnd_mem_txn_id2
             Happender
             ".
    {
      iSplitL "".
      { iPureIntro. eapply log_crash_to_wf; eauto. }
      iSplitL "".
      { iPureIntro. by eapply log_crash_to_post_crash. }
      iFrame "Htxns_ctx'".
      iFrame "Htxns2".
      iSplitL "Hstable_txns2".
      { iThaw "#". iExists _. iFrame "∗#".
        iPureIntro.
        (* we proved this before with [memLog_linv_nextDiskEnd_txn_id_post_crash] *)
        assumption. }
      iExists cs0.
      iSplitDelay.
      { rewrite /wal_linv_durable.
        rewrite sep_exist_r.
        iExists {| diskEnd := diskEnd;
                   locked_diskEnd_txn_id := diskEnd_txn_id;
                   memLog := {| slidingM.log := cs0.(circΣ.upds);
                                slidingM.start := cs0.(circΣ.start);
                                slidingM.mutable := W64 (circΣ.diskEnd cs0);
                             |}
                |}.
        simpl.
        replace (W64 (uint.Z diskEnd)) with diskEnd by word.
        iFrame "HdiskEnd_linv HdiskStart_linv".
        rewrite /memLog_linv /memLog_linv_core.
        iSplitL "installer_pos_mem1 installer_txn_id_mem1
                 logger_pos1 logger_txn_id1
                 diskEnd_mem11 diskEnd_mem_txn_id11
                 installed_pos_mem1 installed_txn_id_mem1
                 Htxns1 HnextDiskEnd_linv".
        - iSplitL ""; first eauto.
          iSplitL ""; first eauto.
          iSplitL "".
          { iPureIntro.
            rewrite /locked_wf/=; split_and!; try word.
            {
              rewrite HdiskEnd_val.
              rewrite /circΣ.diskEnd.
              word.
            }
            rewrite /circ_wf in Hcirc_wf.
            rewrite /slidingM.wf/=; split_and!; try word.
            rewrite /circΣ.diskEnd. word.
          }
          iExists installed_txn_id, _, _, _, _, _, _.
          iFrame.
          simpl.

          rewrite /memLog_linv_pers_core /=.
          iThaw "#".
          replace (W64 (circΣ.diskEnd cs0)) with diskEnd in * by word.
          iSplit.
          {
            iPureIntro.
            rewrite HdiskEnd_val /circΣ.diskEnd.
            word.
          }
          iSplit.
          { word. }
          iFrame "Hinstalled_pos'".
          iFrame "HdiskEnd_stable".
          rewrite length_take.
          replace (S (_ `max` _) `min` _)%nat with
            (S (σ.(log_state.durable_lb) `max` diskEnd_txn_id))%nat;
            last by lia.

          replace (slidingM.endPos _) with diskEnd.
          2: {
            rewrite /slidingM.endPos /=.
            apply (inj uint.Z).
            rewrite HdiskEnd_val.
            rewrite /circΣ.diskEnd.
            unfold circ_wf in *.
            word.
          }
          rewrite /= Nat.sub_0_r.
          iFrame (HdiskEnd_is_txn) "being_installed_start_txn_id_mem_lb".
          iSplit.
          {
            destruct (decide
              (σ.(log_state.durable_lb) ≤ diskEnd_txn_id)%nat
            ).
            {
              rewrite Nat.max_r; last by lia.
              iAssumption.
            }
            rewrite Nat.max_l; last by lia.
            iApply "Hdurable_lb_pos".
          }
          replace (slidingM.memEnd _) with (uint.Z diskEnd) by assumption.
          iSplit.
          {
            iPureIntro.
            apply circ_matches_txns_combine in Hcirc_matches.
            rewrite /memLog_linv_txns /slidingM.logIndex /mwrb.logend /=
              length_take Nat.sub_diag.
            replace (uint.nat diskEnd - _)%nat with (length cs0.(circΣ.upds)).
            2: {
              rewrite /slidingM.logIndex /=.
              unfold circΣ.diskEnd in *.
              word.
            }
            rewrite Nat.min_l; last by lia.
            rewrite /is_memLog_boundaries length_take Nat.min_l; last by lia.
            split.
            {
              intros bndry Hbndry.
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              apply elem_of_cons in Hbndry.
              destruct Hbndry as [->|Hbndry]; first by (simpl; lia).
              inversion Hbndry.
            }
            intros i bndry1 bndry2 Hbndry1 Hbndry2.
            do 3 (destruct i; first by (
              simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
              simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2;
              simpl; (split; first by lia); (split; first by lia);
              rewrite ?subslice_zero_length -?subslice_complete;
              try (rewrite subslice_take_all; last by lia);
              try apply is_memLog_region_nil;
              try apply Hcirc_matches
            )).
            destruct i.
            2: {
              destruct i; last by inversion Hbndry2.
              simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
              simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2;
              simpl; (split; first by lia); (split; first by lia);
              rewrite ?subslice_zero_length -?subslice_complete;
              apply is_memLog_region_nil.
            }
            simpl in Hbndry1; inversion Hbndry1; subst bndry1; clear Hbndry1;
            simpl in Hbndry2; inversion Hbndry2; subst bndry2; clear Hbndry2.
            simpl.
            split; first by lia.
            split; first by lia.
            rewrite subslice_take Nat.min_id.
            destruct (decide (σ.(log_state.durable_lb) ≤ diskEnd_txn_id)).
            {
              rewrite Nat.max_r; last by lia.
              rewrite !subslice_zero_length.
              apply is_memLog_region_nil.
            }
            rewrite Nat.max_l; last by lia.
            rewrite !subslice_zero_length.
            apply is_memLog_region_nils.
            rewrite -(subslice_app_contig _ (S diskEnd_txn_id))
              in Hdurable_nils; last by lia.
            apply Forall_app in Hdurable_nils.
            intuition.
          }
          iPureIntro.
          replace (take _ _) with (σ'.(log_state.txns)) by reflexivity.
          split; last by word.
          apply txns_mono_lt_last; eauto using log_crash_to_wf.
          rewrite /σ' /=.
          rewrite length_take.
          rewrite Nat.min_l; last by lia.
          rewrite /= Nat.sub_0_r.
          apply is_txn_take.
          assumption.
        - iNamedAccu.
      }
      iNamed 1.
      rewrite Hcirc_name. iFrame "Hcirc".
      rewrite /disk_inv.
      iFrame "cs".
      iExists installed_txn_id, installer_txn_id, diskEnd_txn_id; simpl.
      assert (installed_txn_id <= diskEnd_txn_id) by word.

      iSplitL "being_installed_start_txn1
               already_installed1 Hold_txns Hdata".
      {
        rewrite /is_installed/is_installed_core.
        iExists ∅.
        iFrame "being_installed_start_txn1".
        iFrame "already_installed1".
        iSplitL "".
        { iPureIntro. split_and!; try len. }

        iSplitL "Hold_txns".
        { iDestruct (old_txns_are_get with "Hold_txns Hbeing_installed_txns") as "#Hbeing_installed_txns'".
          { rewrite subslice_length; len. }
          iExactEq "Hbeing_installed_txns'". rewrite /named.
          f_equal.
          rewrite subslice_take_all //.
          lia.
        }

        iApply (big_sepM_mono with "Hdata").
        iIntros (k x Hlookup) "H". rewrite /is_dblock_with_txns.
        iDestruct "H" as (b txn_id' Hinstalled) "(?&?)". iExists b, txn_id'. iFrame.
        iPureIntro.
        split; first by lia.
        split.
        { rewrite take_take. rewrite ->min_l by lia. intuition eauto. }
        intros Hupda.
        simpl in Hupda.
        inversion Hupda.
      }
      iFrame (Hdaddrs_init).
      iDestruct (is_base_disk_crash with "Hbasedisk") as "$".
      { auto. }
      iThaw "#".
      iDestruct (is_installed_txn_crash γ γ' with "circ.start Hinstalled_txn_id_stable") as "$"; first by lia.
      iFrame "Hdurable_txn".
      rewrite /is_durable.
      opose proof (circ_matches_txns_crash (uint.nat diskEnd) _ _ _ _ _ _ _ _ _ _) as Hcirc_matches'; [ | by eauto | ].
      { word. }
      iExists _, _, _; iFrame (Hlog_wf) "∗".
      iPureIntro.
      apply (is_memLog_boundaries_append_txns _ _ _ (
        subslice
          (S (diskEnd_txn_id))
          (S (σ.(log_state.durable_lb) `max` diskEnd_txn_id))%nat
          σ.(log_state.txns)
      )) in Hcirc_matches'.
      rewrite -subslice_from_start subslice_app_contig in Hcirc_matches';
        last by lia.
      rewrite subslice_from_start in Hcirc_matches'.
      assumption.
    }
    {
      rewrite /wal_resources /logger_resources.
      rewrite /installer_inv.
      rewrite /named.
      iThaw "#".
      iDestruct "diskEnd_mem_txn_lb" as "-#diskEnd_mem_txn_lb".
      iClear "#".
      iDestruct (mono_nat_lb_own_le installer_txn_id with "diskEnd_mem_txn_lb") as
          "diskEnd_mem_txn_lb"; first by word.
      iFrame "start_avail diskEnd_avail".
      rewrite Hcirc_name.
      iFrame "Happender".
      repeat first [ iExists _ |
                     rewrite sep_exist_l |
                     rewrite sep_exist_r ].
      rewrite -HdiskEnd_val.
      replace (W64 (uint.Z diskEnd)) with diskEnd by word.
      iFrame.
    }
  }
  {
    iNext. iFrame "HPcirc_tok".
    iSplitR "Hinit".
    { iExists _. iFrame. }
    rewrite /wal_init_ghost_state. by iFrame.
  }
  iModIntro.
  iSplitL "Hncinv".
  { rewrite /N. iApply ncinv_split_l. iApply "Hncinv". }
  iFrame. iModIntro. iIntros "HC".
  iMod ("Hcfupd" with "[$]") as (s0 s1) "(>%&>?&>?&?)".
  iModIntro; iExists _, _. iFrame. eauto.
Qed.

Lemma txns_ctx_gname_eq γ γ' txns :
  txns_ctx_name γ = txns_ctx_name γ' →
  txns_ctx γ txns = txns_ctx γ' txns.
Proof. rewrite /txns_ctx/txn_val => -> //=. Qed.

Ltac show_crash1 := crash_case; eauto.

Ltac show_crash2 :=
  try (crash_case);
  iSplitL ""; first auto;
  iSplitL ""; first auto;
  iFrame; iExists _; iFrame; iExists _, _; iFrame "∗ #".

Global Instance txns_ctx_disc γ x:
  Discretizable (txns_ctx γ x).
Proof.
  rewrite /txns_ctx. apply _.
Qed.

Global Instance is_wal_inner_durable_disc γ s:
  Discretizable (is_wal_inner_durable γ s dinit).
Proof. apply _. Qed.

Global Instance disk_inv_disc γ σ cs:
  Discretizable (disk_inv γ σ cs dinit).
Proof. apply _. Qed.

(* halt at σ0 ~~> σ1 ~recovery, crashes~> σ1  *)

Hint Unfold circΣ.diskEnd : word.

Lemma wal_post_crash_durable_lb:
  ∀ σ : log_state.t,
    wal_post_crash σ
    → ∀ (cs : circΣ.t) (diskEnd : u64) (installed_txn_id diskEnd_txn_id : nat),
      is_txn σ.(log_state.txns) diskEnd_txn_id diskEnd
      → (σ.(log_state.durable_lb) ≤ diskEnd_txn_id)%nat
      → diskEnd_txn_id = (length σ.(log_state.txns) - 1)%nat.
Proof.
  intros σ Hpostcrash cs diskEnd installed_txn_id diskEnd_txn_id Hend_txn Hdurable.
  rewrite /wal_post_crash in Hpostcrash.
  rewrite -Hpostcrash.
  apply is_txn_bound in Hend_txn.
  lia.
Qed.

Lemma wal_post_crash_durable_lb_length_txns:
  ∀ σ : log_state.t,
    wal_post_crash σ →
    σ.(log_state.durable_lb) = (length σ.(log_state.txns) - 1)%nat.
Proof.
  intros σ Hpostcrash.
  rewrite /wal_post_crash in Hpostcrash.
  rewrite -Hpostcrash.
  lia.
Qed.

Theorem wpc_mkLog_recover d γ σ :
  {{{ is_wal_inner_durable γ σ dinit ∗ wal_resources γ }}}
    mkLog (disk_val d) @ ⊤
  {{{ l, RET #l;
       "Hwal_inv_pre" ∷ is_wal_inv_pre l γ σ dinit ∗
       "Hlogger" ∷ (∃ (circ_l: loc), "#Hcirc2" ∷ readonly (l ↦[Walog :: "circ"] #circ_l) ∗
                              logger_inv γ circ_l) ∗
       "Hinstaller" ∷ installer_inv γ
       }}}
  {{{ is_wal_inner_durable γ σ dinit ∗ wal_resources γ }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "(Hcs&Hwalres) HΦ".
  rewrite /mkLog.

  wpc_pures.
  { try (crash_case); iFrame. }

  iNamed "Hcs".
  iNamed "Hdisk".
  iDestruct "Hwalres" as "(Hlogger&Hinstaller)".
  rewrite /logger_resources.
  iNamed "Hlogger".
  wpc_bind (recoverCircular _).

  wpc_apply (wpc_recoverCircular with "[$]").
  iSplit.
  { iLeft in "HΦ". iIntros "(Hcirc&Happend)". iApply "HΦ".
    iSplitR "
      Happend HnotLogging
      HownLoggerPos_logger HownLoggerTxn_logger
      HownDiskEnd_logger HownDiskEndTxn_logger
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
      Hinstaller
    ".
    {
      iSplit; first by auto.
      iSplit; first by auto.
      iFrame. }
    { iFrame. }
  }
  rename diskEnd into oldDiskEnd.

  iIntros "!>" (c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&%&%&%)".

  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.
  iNamed "Hdiskinv".

  set (memLog := {|
                 slidingM.log := upds;
                 slidingM.start := diskStart;
                 slidingM.mutable := uint.Z diskStart + length upds |}).

  iApply wpc_fupd.
  wpc_frame "Hwal_linv Hinstalled HΦ Hcirc Happender HnotLogging
    HownLoggerPos_logger HownLoggerTxn_logger
    HownDiskEnd_logger HownDiskEndTxn_logger
    HownDiskEndMem_logger HownDiskEndMemTxn_logger
    Hdurable Hinstaller Howncs Htxns_ctx γtxns HnextDiskEnd_inv".
  {
    iDestruct "Happender" as (????) "(Haddrs&Hblocks&?)".
    crash_case.
    rewrite /is_wal_inner_durable.
    iFrame "Htxns_ctx γtxns HnextDiskEnd_inv".
    iSplitR "Haddrs Hblocks HnotLogging
      HownLoggerPos_logger HownLoggerTxn_logger
      HownDiskEnd_logger HownDiskEndTxn_logger
      HownDiskEndMem_logger HownDiskEndMemTxn_logger
      Hinstaller".
    {
      iSplit; first by auto.
      iSplit; first by auto.
      iExists _. iFrame "Hwal_linv". iFrame "Hcirc". rewrite /disk_inv. iFrame "Howncs".
      iExists _, _, _. iFrame "∗#". eauto.
    }
    { by iFrame. }
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (ml) "Hlock".
  wp_pures.
  iDestruct (updates_slice_cap_acc with "Hupd_slice") as "[Hupd_slice Hupds_cap]".
  wp_apply (wp_mkSliding _ 1 with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }

  iIntros (lslide) "Hsliding".
  iDestruct (is_sliding_wf with "[$]") as %Hsliding_wf.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (st) "Hwal_state".
  wp_pures.

  wp_pures.
  wp_apply (wp_newCond' with "[$]").
  iIntros (condLogger) "(Hlock&#cond_logger)".
  wp_apply (wp_newCond' with "[$]").
  iIntros (condInstall) "(Hlock&#cond_install)".
  wp_apply (wp_newCond' with "[$]").
  iIntros (condShut) "(Hlock&#cond_shut)".
  wp_apply wp_allocStruct.
  { repeat econstructor. }
  iIntros (l) "Hl". wp_pures. wp_apply (util_proof.wp_DPrintf).
  iApply struct_fields_split in "Hl".
  iNamed "Hl".
  iMod (readonly_alloc_1 with "memLock") as "#memLock".
  iMod (readonly_alloc_1 with "d") as "#d".
  iMod (readonly_alloc_1 with "circ") as "#circ".
  iMod (readonly_alloc_1 with "st") as "#st".
  iMod (readonly_alloc_1 with "condLogger") as "#condLogger".
  iMod (readonly_alloc_1 with "condInstall") as "#condInstall".
  iMod (readonly_alloc_1 with "condShut") as "#condShut".
  wp_pures. iModIntro.
  iNamed 1. iRight in "HΦ".
  iApply ("HΦ").
  iMod (alloc_lock walN _ _ (wal_linv st γ)
          with "[$] [Hwal_state Hwal_linv Hsliding]") as "#lk".
  { rewrite /wal_linv. iNext.
    rewrite /wal_linv_durable. iDestruct "Hwal_linv" as (σls Heq1 Heq2 Hlocked_wf) "Hwal_linv".
    iNamed "Hwal_linv". iExists σls. iFrame.
    rewrite /wal_linv_fields.
    iExists {| memLogPtr := _; shutdown := _; nthread := _ |}.
      iDestruct (struct_fields_split with "Hwal_state") as "Hwal_state".
      iNamed "Hwal_state".
      iFrame. iSplitL "diskEnd".
      { rewrite /named. iExactEq "diskEnd". f_equal.
        do 2 f_equal. word. }
      iSplitL ""; eauto.
      rewrite /named. iExactEq "Hsliding". f_equal.
      subst. eauto.
  }
  iModIntro.
  rewrite /is_wal_inv_pre.
  rewrite /circular_pred.
  rewrite /is_wal_inner.
  iSplitL "Hcirc Hinstalled Hdurable Howncs Htxns_ctx γtxns HnextDiskEnd_inv".
  {
    iDestruct "Howncs" as "(Howncs1&Howncs2)".
    iSplitR "Hcirc Howncs1"; last first.
    { iExists _. iFrame. }
    iSplitL ""; first eauto.
    iSplitL "".
    { rewrite /is_wal_mem.
      iExists {| memLock := _; wal_d := _; circ := _; wal_st := _; condLogger := _;
                 condInstall := _; condShut := _ |}.
      iFrame "#".
    }
    iFrame "∗#". eauto.
  }
  iSplitL "
    Happender HnotLogging
    HownLoggerPos_logger HownLoggerTxn_logger
    HownDiskEnd_logger HownDiskEndTxn_logger
    HownDiskEndMem_logger HownDiskEndMemTxn_logger
  ".
  { iExists _. iFrame "∗#". }
  iFrame "Hinstaller".
Qed.

Definition wal_cfupd_cancel E γ' Prec : iProp Σ :=
  (<bdisc> (|C={E}=>  ∃ s s', ⌜relation.denote log_crash s s' tt⌝ ∗
                                 is_wal_inner_durable γ' s' dinit ∗
                                 wal_resources γ' ∗ ▷ Prec s s')).

Definition wal_cinv E γ γ' Pcrash : iProp Σ :=
  □ (|C={E}=> inv (N.@"wal") (∃ s s',
                                      ⌜relation.denote log_crash s s' tt⌝ ∗
                                       is_wal_inner_crash γ s ∗
                                       wal_ghost_exchange γ γ' ∗
                                       Pcrash s s')).

Lemma post_crash_crash_refl σ :
  wal_post_crash σ →
  relation.denote log_crash σ σ ().
Proof.
  inversion 1 as [Heq]. rewrite /log_crash.
  exists σ (σ.(log_state.durable_lb)).
  { econstructor. lia. }
  repeat econstructor. f_equal.
  destruct σ; simpl. unfold set => //=.
  f_equal.
  simpl in Heq. rewrite Heq firstn_all //.
Qed.

Theorem wpc_MkLog_recover E d γ σ Prec Pcrash (Hpostcrash: wal_post_crash σ):
  ↑walN ⊆ E →
  □ (∀ s s' (Hcrash: relation.denote log_crash s s' ()),
        ▷ P s -∗ |={E ∖ ↑N.@"wal"}=> ▷ Prec s s' ∗ ▷ Pcrash s s') -∗
  {{{ is_wal_inner_durable γ σ dinit ∗ wal_resources γ ∗ ▷ P σ }}}
    MkLog (disk_val d) @ ⊤
  {{{ γ' l, RET #l;
      is_wal P l γ dinit ∗
      wal_cfupd_cancel E γ' Prec ∗
      wal_cinv E γ γ' Pcrash
  }}}
  {{{ (∃ γ' σ0 σ', ⌜relation.denote log_crash σ0 σ' tt⌝ ∗
               is_wal_inner_durable γ' σ' dinit ∗ wal_resources γ' ∗ ▷ Prec σ0 σ') }}}.
Proof.
  iIntros (?) "#Hwand".
  iIntros "!>" (Φ Φc) "(Hdurable&Hres&HP) HΦ".
  rewrite /MkLog.
  iApply wpc_cfupd.
  wpc_pures.
  { iLeft in "HΦ". iIntros "HC".
    iSpecialize ("Hwand" with "[] [$]").
    { iPureIntro. by apply post_crash_crash_refl. }
    iMod (fupd_mask_mono with "Hwand") as "(Hrec&Hcrash)".
    { set_solver. }
    iModIntro.
    iApply "HΦ". iExists _, _, _. iFrame "Hdurable Hres Hrec".
    iPureIntro. by apply post_crash_crash_refl.
  }
  wpc_bind (mkLog _).
  wpc_apply (wpc_mkLog_recover with "[$]").
  iSplit.
  { iLeft in "HΦ".
    iIntros "(Hdurable&Hres)".
    iIntros "HC".
    iSpecialize ("Hwand" with "[] [$]").
    { iPureIntro. by apply post_crash_crash_refl. }
    iMod (fupd_mask_mono with "Hwand") as "(Hrec&Hcrash)".
    { set_solver. }
    iModIntro.
    iApply "HΦ". iExists _, _, _. iFrame "Hdurable Hres Hrec".
    iPureIntro. by apply post_crash_crash_refl.
  }
  iNext. iIntros (l). iNamed 1.
  iMod (wal_crash_obligation_alt E  with "Hwal_inv_pre Hwand HP") as (γ') "(#His_wal&Hcancel&#Hcinv)".
  { auto. }
  iApply (wpc_crash_frame_wand_bdisc with "[-Hcancel] Hcancel"); auto; try lia.
  iApply (wp_wpc_frame').
  iSplitL "HΦ".
  { iApply (and_mono with "HΦ"); last done.
    { iIntros "H1". iIntros "H2 HC".
      iDestruct "H2" as (s0 s1 Hcrash) "(Hinner&Hres&Hrec)".
      iModIntro. iApply "H1". iExists _, _, _.
      iSplit; first eauto.
      iFrame. }
  }
  wp_pures. rewrite /Walog__startBackgroundThreads. wp_pures.
  wp_apply (wp_fork with "[Hlogger]").
  { iNext. iDestruct "Hlogger" as (?) "(Hro&Hlogger)".
    iNamed "Hro".
    wp_loadField.
    by wp_apply (wp_Walog__logger with "[$]").
  }
  wp_pures.
  wp_apply (wp_fork with "[Hinstaller]").
  { iNext.
    by wp_apply (wp_Walog__installer with "[$]").
  }
  wp_pures. iIntros "!> H Hcfupd".
  iApply "H". by iFrame "∗#".
Qed.

End goose_lang.

Section stable.
Context `{!heapGS Σ}.
Context `{!walG Σ}.

Local Instance ghost_var_into_crash {A} `{ghost_varG Σ A} (γ: gname) q (x: A):
  IntoCrash (ghost_var γ q x) (λ _, ghost_var γ q x).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.

Local Instance mono_nat_auth_own_into_crash `{mono_natG Σ} (γ: gname) q (x: nat):
  IntoCrash (mono_nat_auth_own γ q x) (λ _, mono_nat_auth_own γ q x).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.

Local Instance txns_are_into_crash γ n l:
  IntoCrash (txns_are γ n l) (λ _, txns_are γ n l).
Proof.
  rewrite /IntoCrash. iApply post_crash_nodep.
Qed.

Instance is_installed_stable γ d txns installed_txn_id installer_txn_id diskEnd_txn_id :
  IntoCrash (is_installed γ d txns installed_txn_id installer_txn_id diskEnd_txn_id)
            (λ _, is_installed γ d txns installed_txn_id installer_txn_id diskEnd_txn_id).
Proof.
  rewrite /IntoCrash. iNamed 1.
  iNamed "Howninstalled".
  iDestruct "Hbeing_installed_txns" as "-#Hbeing_installed_txns".
  iCrash. iExists _. iFrame "∗%".
Qed.

Instance disk_inv_stable γ s cs dinit:
  IntoCrash (disk_inv γ s cs dinit) (λ _, disk_inv γ s cs dinit).
Proof.
  rewrite /IntoCrash. iNamed 1.
  iDestruct (post_crash_nodep with "circ.start") as "-#circ.start'".
  iDestruct (post_crash_nodep with "circ.end") as "-#circ.end'".
  iDestruct (post_crash_nodep with "Hdurable") as "Hdurable".
  iDestruct (post_crash_nodep with "Hbasedisk") as "-#Hbasedisk'".
  iCrash. iExists _, _, _. iFrame. eauto.
Qed.

Instance is_wal_inner_durable_stable γ s dinit:
  IntoCrash (is_wal_inner_durable γ s dinit) (λ _, is_wal_inner_durable γ s dinit).
Proof.
  rewrite /IntoCrash. iNamed 1. iNamed "Hdisk".
  iDestruct (post_crash_nodep with "HnextDiskEnd_inv") as "HnextDiskEnd_inv".
  iDestruct (post_crash_nodep with "Htxns_ctx") as "Htxns_ctx".
  iDestruct (post_crash_nodep with "Hwal_linv") as "Hwal_linv".
  iCrash. iFrame.
  iSplit; done.
Qed.
End stable.


(* this is not interesting on its own, but is just a test to make sure that the
   wal spec is coherent *)

Import recovery_lifting.

Section recov.
  Context `{!heapGS Σ}.
  Context `{!walG Σ}.

  (* Just a simple example of using idempotence *)
  Theorem wpr_MkLog d γ s dinit:
    wal_post_crash s →
    is_wal_inner_durable γ s dinit -∗
    wal_resources γ -∗
    wpr NotStuck ⊤
        (MkLog (disk_val d))
        (MkLog (disk_val d))
        (λ _, True%I)
        (λ _, True%I)
        (λ _ _, True%I).
  Proof.
    iIntros (?) "His_wal_inner_durable Hres".
    iApply (idempotence_wpr NotStuck ⊤ _ _ (λ _, True)%I (λ _, True)%I (λ _ _, True)%I
                            (λ _, ∃ σ' γ' (Hpost: wal_post_crash σ'),
                                is_wal_inner_durable γ' σ' dinit ∗ wal_resources γ' ∗ ▷ True)%I
                            with "[His_wal_inner_durable Hres] []").
    { wpc_apply (wpc_MkLog_recover dinit (λ _, True)%I _ _ _ _ (λ _ _, True)%I (λ _ _, True)%I
                   with "[] [$His_wal_inner_durable $Hres]"); auto 10.
      iSplit.
      * iDestruct 1 as (????) "(?&?&_)".
        unshelve (iExists _, _, _; iFrame; eauto).
        { eapply log_crash_to_post_crash; eauto. }
      * eauto.
    }
    iModIntro. iIntros (????) "H".
    (* FIXME: we bundle local and global, but [idempotence_wpr] quantifies only over the local part...
       and we want the terms below to pick up the new local part. Sadly the let-binding in the
       statement of [idempotence_wpr] is lost so we have to introduce it again ourselves here. *)
    set (hG' := HeapGS _ _ _).
    iDestruct "H" as (σ'') "Hstart".
    iNext.
    iDestruct "Hstart" as (??) "(H1&Hres&_)".
    rewrite is_wal_inner_durable_stable.
    iDestruct (post_crash_nodep with "Hres") as "Hres".
    iCrash. iIntros "_". iSplit; first done.
    { wpc_apply (wpc_MkLog_recover dinit (λ _, True)%I _ _ _ _ (λ _ _, True)%I (λ _ _, True)%I
                 with "[] [$H1 $Hres]"); auto 10.
      iSplit.
      * iDestruct 1 as (????) "(?&?&_)".
        unshelve (iExists _, _, _; iFrame; eauto).
        { eapply log_crash_to_post_crash; eauto. }
      * eauto.
    }
  Qed.
End recov.
