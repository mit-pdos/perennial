From RecordUpdate Require Import RecordUpdate.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.
From Perennial.goose_lang Require Import crash_modality.
Open Scope Z.

Section goose_lang.
Context `{!heapG Σ}.
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

    "installer_pos_mem" ∷ ghost_var γnew.(installer_pos_mem_name) 1 0%nat ∗
    "installer_txn_id_mem" ∷ ghost_var γnew.(installer_txn_id_mem_name) 1 0%nat ∗

    "logger_pos" ∷ ghost_var γnew.(logger_pos_name) 1 0%nat ∗
    "logger_txn_id" ∷ ghost_var γnew.(logger_txn_id_name) 1 0%nat ∗

    "installed_pos_mem" ∷ ghost_var γnew.(installed_pos_mem_name) 1 0%nat ∗
    "installed_txn_id_mem" ∷ ghost_var γnew.(installed_txn_id_mem_name) 1 0%nat ∗

    "diskEnd_mem" ∷ fmcounter γnew.(diskEnd_mem_name) 1 0%nat ∗
    "diskEnd_mem_txn_id" ∷ fmcounter γnew.(diskEnd_mem_txn_id_name) 1 0%nat ∗
    "being_installed_start_txn" ∷ fmcounter γnew.(being_installed_start_txn_name) 1 0%nat ∗
    "being_installed_end_txn" ∷ ghost_var γnew.(being_installed_end_txn_name) 1 0%nat ∗
    "already_installed" ∷ ghost_var γnew.(already_installed_name) 1 (∅ : gset Z)  ∗
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

Lemma is_wal_inner_durable_init (bs: list Block) :
  0 d↦∗ repeat block0 513 ∗
  513 d↦∗ bs ={⊤}=∗
  let s := (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0) in
  ∃ γ, is_wal_inner_durable γ s dinit.
Proof.
Admitted.

Existing Instance own_into_crash.

Definition log_crash_to σ diskEnd_txn_id :=
  set log_state.durable_lb (λ _, diskEnd_txn_id)
      (set log_state.txns (take (S diskEnd_txn_id)) σ).

Lemma crash_to_diskEnd γ cs σ diskEnd_txn_id installed_txn_id :
  is_durable_txn (Σ:=Σ) γ cs σ.(log_state.txns) diskEnd_txn_id  σ.(log_state.durable_lb) -∗
  is_durable γ cs σ.(log_state.txns) installed_txn_id diskEnd_txn_id -∗
  ⌜relation.denote log_crash σ (log_crash_to σ diskEnd_txn_id) tt⌝.
Proof.
  iNamed 1.
  rewrite /is_durable.
  iNamed 1.
  iPureIntro.
  simpl.
  eexists _ diskEnd_txn_id; simpl; monad_simpl.
  constructor.
  split; try lia.
  eapply is_txn_bound; eauto.
Qed.

Ltac iPersist H :=
  let H' := (eval cbn in (String.append "#" H)) in
  iDestruct H as H'.

(* TODO(tej): why isn't this true any more? *)
(*
Instance is_installed_Durable txns txn_id diskEnd_txn_id installed_txn_id :
  IntoCrash (is_installed_read dinit txns txn_id diskEnd_txn_id installed_txn_id)
            (λ _, is_installed_read dinit txns txn_id diskEnd_txn_id installed_txn_id).
Proof. apply _. Qed.
*)

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
  intros Hincl a. rewrite -?elem_of_list_In.
  intros (?&?&Hin')%elem_of_list_fmap. subst.
  apply elem_of_list_fmap. eexists; split; eauto.
  move: Hin'. rewrite ?elem_of_list_In. eauto.
Qed.

Lemma log_crash_to_wf σ σ' x :
  wal_wf σ →
  relation.denote log_crash σ σ' x →
  wal_wf σ'.
Proof.
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
  rewrite take_length. lia.
Qed.

Lemma is_txn_implies_non_empty_txns γ cs txns installed_txn_id:
  is_txn txns installed_txn_id (start cs) →
  txns ≠ [].
Proof.
  rewrite /is_txn.
  rewrite fmap_Some.
  intros (?&Hlookup&_).
  apply elem_of_list_lookup_2 in Hlookup.
  destruct txns; eauto.
  set_solver.
Qed.

(* XXX: I think this suggests that we're going to have to require the initial state
   to have a non empty list of txns. *)
Lemma is_installed_txn_implies_non_empty_txns γ cs txns installed_txn_id lb:
  is_installed_txn (Σ:=Σ) γ cs txns installed_txn_id lb -∗
  ⌜ txns ≠ [] ⌝.
Proof. iNamed 1. iPureIntro. by eapply is_txn_implies_non_empty_txns. Qed.

Lemma circ_matches_txns_crash cs txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id:
  circ_matches_txns cs txns installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id →
  circ_matches_txns cs (take (S diskEnd_txn_id) txns) installed_txn_id installer_pos installer_txn_id diskEnd_mem diskEnd_mem_txn_id diskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns.
  destruct 1 as [Heq Hlb].
  split.
  - admit.
  - admit.
  (* intros d. rewrite Heq /subslice take_idemp //=. *)
Admitted.

Lemma is_txn_from_take_is_txn n txns id pos:
  is_txn (take n txns) id pos →
  is_txn txns id pos.
Proof.
  rewrite /is_txn.
  destruct (decide (id < n)%nat).
  { by rewrite -> lookup_take by lia. }
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
  rewrite -> lookup_take by lia; auto.
Qed.

Lemma is_highest_txn_take txns txn_id pos :
  is_highest_txn txns txn_id pos →
  is_highest_txn (take (S txn_id) txns) txn_id pos.
Proof.
  rewrite /is_highest_txn /is_txn. intros (Hlook&Hle); split.
  - rewrite -> lookup_take by lia; auto.
  - intros txn_id'. rewrite ?fmap_Some.
    intros (x&Hlookup&Hpos); subst.
    eapply lookup_take_Some in Hlookup; lia.
Qed.

Lemma alloc_wal_init_ghost_state γ γcirc :
  ⊢ |==> ∃ γnew, "%Hbase_name" ∷ ⌜γnew.(base_disk_name) = γ.(base_disk_name)⌝ ∗
                 "%Hcirc_name" ∷ ⌜γnew.(circ_name) = γcirc⌝ ∗
                 "Hinit" ∷ wal_init_ghost_state γnew.
Proof.
  iMod (ghost_var_alloc 0%nat) as (installer_pos_name) "Hinstalled_pos".
  iMod (ghost_var_alloc 0%nat) as (installer_txn_id_name) "Hinstalled_txn_id".

  iMod (ghost_var_alloc 0%nat) as (installer_pos_mem_name) "?".
  iMod (ghost_var_alloc 0%nat) as (installer_txn_id_mem_name) "?".

  iMod (ghost_var_alloc 0%nat) as (logger_pos_name) "?".
  iMod (ghost_var_alloc 0%nat) as (logger_txn_id_name) "?".

  iMod (ghost_var_alloc 0%nat) as (installed_pos_mem_name) "?".
  iMod (ghost_var_alloc 0%nat) as (installed_txn_id_mem_name) "?".

  iMod (fmcounter_alloc 0%nat) as (diskEnd_mem_name) "?".
  iMod (fmcounter_alloc 0%nat) as (diskEnd_mem_txn_id_name) "?".

  iMod (ghost_var_alloc (∅ : gset Z)) as (already_installed_name) "Halready_installed".
  iMod (fmcounter_alloc 0%nat) as (being_installed_start_txn_name) "Hbeing_start".
  iMod (ghost_var_alloc 0%nat) as (being_installed_end_txn_name) "Hbeing_end".
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
            being_installed_end_txn_name := being_installed_end_txn_name;
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
            installed_pos_mem_name := installed_pos_mem_name;
            installed_txn_id_mem_name := installed_txn_id_mem_name;
            base_disk_name := γ.(base_disk_name) |}; simpl.
  by iFrame.
Qed.

Lemma is_base_disk_crash γ γ' d :
  γ'.(base_disk_name) = γ.(base_disk_name) →
  is_base_disk γ d -∗ is_base_disk γ' d.
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
    iFrame "#∗".
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

Lemma init_stable_txns γstable_txn_ids_name (installed_txn_id diskEnd_txn_id : nat) :
  map_ctx   γstable_txn_ids_name 1 (∅ : gmap nat unit) -∗
  |==> "Hstable_txns" ∷ map_ctx γstable_txn_ids_name 1 (gset_to_gmap () {[diskEnd_txn_id; installed_txn_id]}) ∗
       "#HdiskEnd_stable" ∷ diskEnd_txn_id [[γstable_txn_ids_name]]↦ro () ∗
       "#Hinstalled_txn_id_stable" ∷ installed_txn_id [[γstable_txn_ids_name]]↦ro ().
Proof.
  iIntros "Hstable_txns".
  iMod (map_alloc_ro_set with "Hstable_txns") as "[$ Hro]".
  iModIntro.

  iDestruct (big_sepS_elem_of with "Hro") as "#$"; first by set_solver.
  iDestruct (big_sepS_elem_of with "Hro") as "#$"; first by set_solver.
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
  rewrite -> lookup_take by lia.
  auto.
Qed.

Lemma is_durable_txn_crash γ γ' cs txns diskEnd_txn_id durable_lb :
  is_durable_txn γ cs txns diskEnd_txn_id durable_lb -∗
  diskEnd_txn_id [[γ'.(stable_txn_ids_name)]]↦ro () -∗
  is_durable_txn γ' cs (take (S diskEnd_txn_id) txns) diskEnd_txn_id diskEnd_txn_id.
Proof.
  iNamed 1. iIntros "#Hend_txn_stable'".
  rewrite /is_durable_txn.
  iExists diskEnd; iFrame "%#".
  iSplit; first (iPureIntro; lia).
  iPureIntro.
  apply is_txn_take; auto.
Qed.

Definition logger_resources γ : iProp Σ :=
  (* subset of logger that doesn't include [is_circular_appender], which depends
  on in-memory state *)
  "HnotLogging" ∷ thread_own γ.(diskEnd_avail_name) Available ∗
  "HownLoggerPos_logger" ∷ (∃ (logger_pos : u64), ghost_var γ.(logger_pos_name) (1/2) logger_pos) ∗
  "HownLoggerTxn_logger" ∷ (∃ (logger_txn_id : nat), ghost_var γ.(logger_txn_id_name) (1/2) logger_txn_id).

(* TODO: reconstruct this on crash *)
Definition wal_resources γ : iProp Σ :=
  logger_resources γ ∗ installer_inv γ.

(* TODO: recovery needs to produce this *)
Definition background_inv l γ : iProp Σ :=
  ∃ (circ_l: loc),
    l ↦[Walog.S :: "circ"] #circ_l ∗
    logger_inv γ circ_l ∗
    installer_inv γ.

(* txns_ctx factory: a way to remember that some [txn_val]s are valid even after
a crash *)
Section txns_factory.

(* the crux of this approach is this resource, which has an auth over the old
transactions in [γ] and connects them to the transactions in [γ']. [txn_val]s in
[γ] that are prior to the crash point can be used to get one in the new
generation. *)
Definition old_txn_factory γ crash_txn γ' : iProp Σ :=
  ∃ txns, txns_ctx γ txns ∗
  [∗ list] i↦txn ∈ (take (S crash_txn) txns), list_el γ'.(txns_ctx_name) i txn.

Lemma txns_ctx_make_factory γ txns crash_txn γ' :
  txns_ctx γ txns -∗
  txns_ctx γ' (take (S crash_txn) txns) -∗
  old_txn_factory γ crash_txn γ' ∗ txns_ctx γ' (take (S crash_txn) txns).
Proof.
  rewrite {2 3}/txns_ctx /list_ctx /old_txn_factory.
  iIntros "Htxn [Hctx #Hels]".
  iFrame "#∗".
  iExists _; iFrame "#∗".
Qed.

Lemma old_txn_get γ γ' crash_txn txn_id txn :
  (txn_id ≤ crash_txn)%nat →
  old_txn_factory γ crash_txn γ' -∗
  txn_val γ txn_id txn -∗
  txn_val γ' txn_id txn.
Proof.
  iIntros (?) "Hfactory Hel".
  iDestruct "Hfactory" as (txns) "[Hctx Hels]".
  iDestruct (alist_lookup with "Hctx Hel") as %Hloookup.
  iDestruct (big_sepL_lookup with "Hels") as "$".
  rewrite -> lookup_take by lia. done.
Qed.

Lemma old_txns_are_get γ γ' crash_txn start txns_sub :
  (start + length txns_sub ≤ S crash_txn)%nat →
  old_txn_factory γ crash_txn γ' -∗
  txns_are γ start txns_sub -∗
  txns_are γ' start txns_sub.
Proof.
  iIntros (Hbound) "Hfactory Htxns".
  rewrite /txns_are /list_subseq.
  iInduction txns_sub as [|txn txns] "IH" forall (start Hbound).
  - rewrite !big_sepL_nil //.
  - simpl in Hbound.
    rewrite !big_sepL_cons.
    iDestruct "Htxns" as "[Htxn Htxns]".
    rewrite Nat.add_0_r.
    iDestruct (old_txn_get with "Hfactory Htxn") as "#$"; first by lia.
    setoid_rewrite <- Nat.add_succ_comm.
    iApply ("IH" with "[%] [$] Htxns").
    lia.
Qed.
End txns_factory.


Lemma diskEnd_linv_post_crash γ' diskEnd Q :
  int.Z (U64 diskEnd) = diskEnd →
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
  replace (int.Z (U64 diskEnd)) with diskEnd by auto.
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
  iDestruct (start_is_to_at_least with "[$]") as "[H #Hatleast]".
  iMod (thread_own_get with "Hctx Havail") as "(Hctx & _ & Hused)".
  rewrite /diskEnd_linv.
  iMod (thread_own_put (start_is γ'.(circ_name) (1/2) start) with
        "Hctx Hused H") as "[$ $]".
  by iFrame "#".
Qed.

Lemma memLog_linv_nextDiskEnd_txn_id_post_crash γ diskEnd diskEnd_txn_id installed_txn_id :
  (installed_txn_id ≤ diskEnd_txn_id)%nat →
  map_ctx γ.(stable_txn_ids_name) (1/2) (gset_to_gmap () {[diskEnd_txn_id; installed_txn_id]}) -∗
  txn_pos γ diskEnd_txn_id diskEnd -∗
  diskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro () -∗
  memLog_linv_nextDiskEnd_txn_id γ diskEnd diskEnd_txn_id.
Proof.
  iIntros (Hbound) "Hctx #Hpos #HdiskEnd_stable".
  iExists _; iFrame "#∗".
  iPureIntro.
  intros ??.
  apply lookup_gset_to_gmap_None.
  assert (txn_id ≠ diskEnd_txn_id) by lia.
  assert (txn_id ≠ installed_txn_id) by lia.
  set_solver.
Qed.

Lemma is_durable_txn_get_txn_pos γ' cs txns diskEnd_txn_id durable_lb :
  is_durable_txn γ' cs txns diskEnd_txn_id durable_lb -∗
  txns_ctx γ' txns -∗
  txn_pos γ' diskEnd_txn_id (U64 (circΣ.diskEnd cs)).
Proof.
  iNamed 1.
  iIntros "Hctx".
  iDestruct (txns_ctx_txn_pos with "Hctx") as "$"; eauto.
  replace (U64 (circΣ.diskEnd cs)) with diskEnd by word; auto.
Qed.

(* Called after wpc for recovery is completed, so l is the location of the wal *)
Lemma wal_crash_obligation_alt Prec Pcrash l γ s :
  is_wal_inv_pre l γ s dinit -∗
  □ (∀ s s' (Hcrash: relation.denote log_crash s s' ()),
        ▷ P s -∗ |0={⊤ ∖ ↑N.@"wal"}=> ▷ Prec s' ∗ ▷ Pcrash s s') -∗
  P s -∗
  |={⊤}=> ∃ γ', is_wal P l γ dinit ∗
                (<bdisc> (C -∗ |0={⊤}=> ▷ ∃ s, ⌜wal_post_crash s⌝ ∗
                                         (* NOTE: need to add the ghost state that the logger will need *)
                                         is_wal_inner_durable γ' s dinit ∗
                                         wal_resources γ' ∗ Prec s)) ∗
                □ (C -∗ |0={⊤}=> inv (N.@"wal") (∃ s s',
                                           ⌜relation.denote log_crash s s' tt⌝ ∗
                                           is_wal_inner_crash γ s ∗
                                           wal_ghost_exchange γ γ' ∗
                                           Pcrash s s')).
Proof.
  iIntros "Hinv_pre #Hwand HP".
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
  iMod (ncinv_cinv_alloc (N.@"wal") ⊤ ⊤
         ((∃ σ, is_wal_inner l γ σ dinit ∗ P σ) ∗
                wal_init_ghost_state γ' ∗ Pcirc_tok)
         (∃ σ σ',
               ⌜relation.denote log_crash σ σ' tt⌝ ∗
               is_wal_inner_crash γ σ ∗
               wal_ghost_exchange γ γ' ∗
               Pcrash σ σ')%I
         (∃ s,
                 ⌜wal_post_crash s⌝ ∗ (is_wal_inner_durable γ' s dinit) ∗ wal_resources γ' ∗ Prec s)%I with
            "[] [Hinner HP Hinit HPcirc_tok]") as "(Hncinv&Hcfupd&Hcinv)".
  { solve_ndisj. }
  { iModIntro. iIntros "(H1&>Hinit&Htok) #HC".
    iMod ("HPcirc_tok_wand" with "[$]") as "H".
    iSpecialize ("H" with "[$]").
    iMod (fupd_level_mask_mono with "H") as (cs0') "(Hcirc&Hcirc_resources&>Hcirc_pred)"; first solve_ndisj.
    iDestruct "H1" as (σ) "(His_wal_inner&HP)".
    iDestruct "His_wal_inner" as "(>%Hwf&_&>?&>?&>?&>?)"; iNamed.
    iNamed "Hdisk".
    iNamed "Hdisk".
    rewrite /circular_pred.
    iDestruct (ghost_var_agree with "Howncs Hcirc_pred") as %<-.

    iNamed "Hinit".
    iMod (init_stable_txns γ'.(stable_txn_ids_name) installed_txn_id diskEnd_txn_id with "[$]") as "Hstable". iNamed "Hstable".

    set (σ':= log_crash_to σ diskEnd_txn_id).
    iDestruct (crash_to_diskEnd with "circ.end Hdurable") as %Htrans.
    iNamed "Hdurable".
    iNamed "Hinstalled". iNamed "Howninstalled".

    iMod (ghost_var_update installer_pos with "installer_pos") as "[installer_pos1 installer_pos2]".
    iMod (ghost_var_update installer_txn_id with "installer_txn_id") as "[installer_txn_id1 installer_txn_id2]".
    iMod (ghost_var_update ∅ with "already_installed") as "[already_installed1 already_installed2]".
    iMod (fmcounter_update diskEnd_mem with "diskEnd_mem") as "[[diskEnd_mem1 diskEnd_mem2] #diskEnd_mem_lb]"; first by lia.
    iMod (fmcounter_update diskEnd_mem_txn_id with "diskEnd_mem_txn_id") as "[[diskEnd_mem_txn_id1 diskEnd_mem_txn_id2] #diskEnd_mem_txn_lb]"; first by lia.
    iMod (fmcounter_update being_installed_start_txn_id with "being_installed_start_txn") as "[[being_installed_start_txn1 being_installed_start_txn2] #being_installed_start_txn_id_mem_lb]"; first by lia.
    iMod (ghost_var_update being_installed_end_txn_id with "being_installed_end_txn") as "[being_installed_end_txn1 being_installed_end_txn2]".
    iMod (txns_ctx_app (take (S diskEnd_txn_id) σ.(log_state.txns)) with "txns_ctx") as "Htxns_ctx'".
    rewrite app_nil_l.
    iMod (ghost_var_update σ'.(log_state.txns) with "txns") as "[Htxns1 Htxns2]".

    iDestruct (txns_ctx_make_factory with "Htxns_ctx Htxns_ctx'") as "[Hold_txns Htxns_ctx']".

    iDestruct (is_durable_txn_crash with "circ.end [$]") as "#Hdurable_txn".

    iDestruct (is_durable_txn_get_txn_pos with "Hdurable_txn Htxns_ctx'") as "#HdiskEnd_pos".

    iNamed "circ.end".

    replace (U64 (circΣ.diskEnd cs0)) with diskEnd by word.

    iPoseProof "circ.start" as "#tmp"; iNamed "tmp".
    iDestruct "Hcirc_resources" as "(Hcirc_start&Hcirc_diskEnd & Happender)".

    iMod (diskEnd_linv_post_crash _ (int.Z diskEnd)
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
    iDestruct (memLog_linv_nextDiskEnd_txn_id_post_crash with
               "Hstable_txns1 HdiskEnd_pos [$]")
              as "HnextDiskEnd_linv"; first by lia.
    iFreeze "# Hdata".

    (* TODO(tej): these are my best guesses from the invariant, but they'll be
    driven by a lemma that re-establishes [memLog_linv_pers_core] using maybe
    just [circ_matches_txns] *)
    iMod (ghost_var_update (int.nat cs0.(circΣ.start)) with "installer_pos_mem")
         as "[installer_pos_mem1 installer_pos_mem2]".
    iMod (ghost_var_update (int.nat cs0.(circΣ.start)) with "installed_pos_mem")
         as "[installed_pos_mem1 installed_pos_mem2]".
    iMod (ghost_var_update installed_txn_id with "installed_txn_id_mem")
         as "[installed_txn_id_mem1 installed_txn_id_mem2]".
    iMod (ghost_var_update installed_txn_id with "installer_txn_id_mem")
         as "[installer_txn_id_mem1 installer_txn_id_mem2]".
    iMod (ghost_var_update (Z.to_nat (circΣ.diskEnd cs0)) with "logger_pos")
        as "[logger_pos1 logger_pos2]".
    iMod (ghost_var_update diskEnd_txn_id with "logger_txn_id")
        as "[logger_txn_id1 logger_txn_id2]".


    (*
memLog_linv_pers_core facts:

todo:
    "#Hlinv_pers" ∷ memLog_linv_pers_core γ σ diskEnd diskEnd_txn_id installed_txn_id_mem nextDiskEnd_txn_id txns logger_pos logger_txn_id installer_pos_mem installer_txn_id_mem ∗
done:
    "Howntxns" ∷ ghost_var γ.(txns_name) (1/2) txns ∗
    "HownDiskEndMem_linv" ∷ fmcounter γ.(diskEnd_mem_name) (1/2) (int.nat diskEnd) ∗
    "HownDiskEndMemTxn_linv" ∷ fmcounter γ.(diskEnd_mem_txn_id_name) (1/2) diskEnd_txn_id ∗
    "HnextDiskEnd" ∷ memLog_linv_nextDiskEnd_txn_id γ σ.(slidingM.mutable) nextDiskEnd_txn_id ∗
    "HownInstallerPosMem_linv" ∷ ghost_var γ.(installer_pos_mem_name) (1/2) installer_pos_mem ∗
    "HownInstallerTxnMem_linv" ∷ ghost_var γ.(installer_txn_id_mem_name) (1/2) installer_txn_id_mem ∗
    "HownInstalledPosMem_linv" ∷ ghost_var γ.(installed_pos_mem_name) (1/2) σ.(slidingM.start) ∗
    "HownInstalledTxnMem_linv" ∷ ghost_var γ.(installed_txn_id_mem_name) (1/2) installed_txn_id_mem
    "HownLoggerPos_linv" ∷ ghost_var γ.(logger_pos_name) (1/2) logger_pos ∗
    "HownLoggerTxn_linv" ∷ ghost_var γ.(logger_txn_id_name) (1/2) logger_txn_id ∗
     *)

    iThaw "Hwand".
    iMod ("Hwand" $! σ σ' with "[//] HP") as "(HPrec&HPcrash)".
    iClear "Hwand".
    iSplitL "HPcrash".
    { iModIntro. iExists σ, σ'. iFrame. iNext. eauto. }
    iExists σ'. iFrame "HPrec".
    do 2iModIntro.
    iSplitL "".
    { iPureIntro. by eapply log_crash_to_post_crash. }


    iSplitR "start_avail diskEnd_avail
             being_installed_start_txn2 being_installed_end_txn2
             ".
    {
    iSplitL "".
    { iPureIntro. eapply log_crash_to_wf; eauto. }
    iSplitL "".
    { iPureIntro. by eapply log_crash_to_post_crash. }
    iSplitDelay.
    { rewrite /wal_linv_durable.
      rewrite sep_exist_r.
      iExists {| diskEnd := diskEnd;
                 locked_diskEnd_txn_id := diskEnd_txn_id;
                 memLog := {| slidingM.log := cs0.(circΣ.upds);
                              slidingM.start := cs0.(circΣ.start);
                              slidingM.mutable := U64 (circΣ.diskEnd cs0);
                           |}
              |}.
      simpl.
      replace (U64 (int.Z diskEnd)) with diskEnd by word.
      iFrame "HdiskEnd_linv HdiskStart_linv".
      rewrite /memLog_linv /memLog_linv_core.

      rewrite sep_exist_r; iExists installed_txn_id.
      iSplitL "installer_pos_mem1 installed_txn_id_mem1 installer_txn_id_mem1".
      - admit. (* prove this *)
      - iNamedAccu.
    }
    iNamed 1.
    iExists cs0. rewrite Hcirc_name. iFrame "Hcirc".
    rewrite /disk_inv.
    simpl.
    iExists installed_txn_id, diskEnd_txn_id; simpl.
    assert (installed_txn_id <= diskEnd_txn_id) by word.

    iSplitL "being_installed_start_txn1 being_installed_end_txn1
             already_installed1 Hold_txns Hdata".
    {
      rewrite /is_installed/is_installed_core.
      iExists being_installed_start_txn_id, being_installed_end_txn_id, ∅.
      iFrame "being_installed_start_txn1".
      iFrame "being_installed_end_txn1".
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
      split_and!; try lia.
      - set_solver.
      - rewrite take_take. rewrite ->min_l by lia. intuition eauto.
    }
    iFrame (Hdaddrs_init).
    iDestruct (is_base_disk_crash with "Hbasedisk") as "$".
    { auto. }
    iThaw "#".
    iDestruct (is_installed_txn_crash γ γ' with "circ.start Hinstalled_txn_id_stable") as "$"; first by lia.
    iFrame "Hdurable_txn".
    efeed pose proof (circ_matches_txns_crash) as Hcirc_matches'; first by eauto.
    iExists _, _, _, _; iFrame (Hcirc_matches') "∗".
  }
  {
    rewrite /wal_resources.
    rewrite /installer_inv.
    iSplitL "diskEnd_avail".
    { iFrame.
      admit. (* more ghost vars, residual from above proof *) }
    iExists being_installed_start_txn_id, being_installed_end_txn_id.
    iFrame.
    admit. (* more ghost vars, residual from above proof *)
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
  iFrame.
  all: fail "goals remaining".
Admitted.

(*
Lemma is_wal_inner_durable_post_crash l γ σ cs P':
  (∀ σ', relation.denote (log_crash) σ σ' tt → IntoCrash (P σ) (P' σ')) →
  "Hinner" ∷ is_wal_inner l γ σ dinit ∗ "HP" ∷ P σ ∗
  "Hcirc" ∷ is_circular_state γ.(circ_name) cs ∗ "γcs" ∷ circular_pred γ cs  -∗
  post_crash (λ hG, ∃ σ', ⌜ relation.denote (log_crash) σ σ' tt ⌝ ∗
                            is_wal_inner_durable γ σ' dinit ∗
                            P' σ' hG).
Proof.
  rewrite /circular_pred.
  iIntros (Hcrash). iNamed 1.
  rewrite /is_wal_inner_durable.
  iNamed "Hinner".
  iNamed "Hdisk".
  iNamed "Hdisk".

  unify_ghost_var γ.(cs_name).
  clear cs; rename cs0 into cs.
  iDestruct (is_installed_weaken_read with "Hinstalled") as (new_installed_txn_id) "Hinstalled".
  set (σ':= log_crash_to σ diskEnd_txn_id).
  iDestruct (crash_to_diskEnd with "circ.end Hdurable") as %Htrans.
  specialize (Hcrash _ Htrans).
  iNamed "circ.start".
  iNamed "circ.end".
  iNamed "Hdurable".
  iCrash.
  iExists _; iFrame.
  iSplit.
  { eauto. }
  iSplit.
  { iPureIntro.
    eapply log_crash_to_wf; eauto. }
  iSplit.
  { iPureIntro.
    eapply log_crash_to_post_crash; eauto. }
  iExists cs; iFrame.
  iExists installed_txn_id, diskEnd_txn_id; simpl.
  assert (installed_txn_id <= diskEnd_txn_id) by word.
  admit.
  (*
  iSplitL "Hinstalled".
  { iDestruct "Hinstalled" as (new_installed_txn_id) "[% Hinstalled]".
    rewrite /is_installed_read.
    iExists _.
    iSplit.
    { admit. }
    iApply (big_sepM_mono with "Hinstalled").
    iIntros (a b0 Hlookup) "H".
    iDestruct "H" as (b) "(%Happly_upds&Ha&%Ha_bound)".
    iExists b; iFrame "% ∗".
    iPureIntro.
    destruct Happly_upds as (txn_id'&Hbound&Happly).
    exists txn_id'; split_and!; auto; autorewrite with len; try lia.
    2: {
      rewrite take_take.
      replace (S txn_id' `min` S diskEnd_txn_id)%nat with (S txn_id') by lia.
      auto.
    }
    admit.
  }
  *)

(*
  iPureIntro. split_and!.
  - apply circ_matches_txns_crash; auto.
  - naive_solver.
  - destruct Hcirc_start as (Hcirc_start1&Hcirc_start2).
    split; auto.
    * destruct Hcirc_start2 as (Htxn&?). rewrite /is_txn.
      rewrite -Htxn. f_equal.
      rewrite lookup_take; eauto. lia.
    * intros.
      destruct Hcirc_start2 as (Htxn&Hhigh). eapply Hhigh.
      eapply is_txn_from_take_is_txn; eauto.
  - destruct Hcirc_end as (x&?&?&?).
    exists x; split_and!; eauto.
    apply is_txn_take; auto.
Qed.
*)
Admitted.
*)

Lemma is_wal_post_crash γ P' l:
  (∀ σ σ', relation.denote (log_crash) σ σ' tt →
           IntoCrash (P σ) (P' σ')) →
  is_wal P l γ dinit ={↑walN, ∅}=∗ ▷
  post_crash (λ hG, ∃ σ σ', ⌜ relation.denote (log_crash) σ σ' tt ⌝ ∗ is_wal_inner_durable γ σ' dinit ∗ P' σ' hG).
Proof.
Abort.

Lemma txns_ctx_gname_eq γ γ' txns :
  txns_ctx_name γ = txns_ctx_name γ' →
  txns_ctx γ txns = txns_ctx γ' txns.
Proof. rewrite /txns_ctx/gen_heap_ctx/txn_val => -> //=. Qed.

Ltac show_crash1 := crash_case; eauto.

Ltac show_crash2 :=
  try (crash_case);
  iSplitL ""; first auto;
  iSplitL ""; first auto;
  iFrame; iExists _; iFrame; iExists _, _; iFrame "∗ #".

Global Instance is_wal_inner_durable_disc γ σ:
  Discretizable (is_wal_inner_durable γ σ dinit).
Proof.
  (* TODO: figure out what part of wal_linv_durable is not easily
  Discretizable *)
Abort.

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

Lemma txns_mono_lt_last σ diskEnd :
  wal_wf σ →
  is_txn σ.(log_state.txns) (length σ.(log_state.txns) - 1) diskEnd →
  Forall (λ pos, int.Z pos ≤ int.Z diskEnd) σ.(log_state.txns).*1.
Proof.
  intros Hwf Htxn.
  apply Forall_forall => pos Hin.
  apply elem_of_list_lookup in Hin as [txn_id Hlookup].
  assert (is_txn σ.(log_state.txns) txn_id pos).
  { rewrite /is_txn.
    rewrite -list_lookup_fmap //. }
  eapply (wal_wf_txns_mono_pos' (txn_id1:=txn_id)); eauto.
  apply is_txn_bound in H.
  lia.
Qed.


(* TODO: adapt this theorem to new generation management (proof still has some
   useful memlog reconstruction stuff) *)

  (*
Theorem wpc_mkLog_recover k (d : loc) γ σ :
  {{{ is_wal_inner_durable γ σ dinit }}}
    mkLog #d @ NotStuck; k; ⊤
  {{{ γ' l, RET #l;
       "Hwal_inv_pre" ∷ is_wal_inv_pre l γ' σ dinit ∗
       "Hlogger" ∷ (∃ (circ_l: loc), "#Hcirc2" ∷ readonly (l ↦[Walog.S :: "circ"] #circ_l) ∗
                              logger_inv γ circ_l) ∗
       "Hinstaller" ∷ installer_inv γ
       }}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ dinit }}}.
Proof.
  clear P.
  iIntros (Φ Φc) "Hcs HΦ".
  rewrite /mkLog.

  wpc_pures; first by show_crash1.

  iNamed "Hcs".
  iNamed "Hdisk".
  wpc_bind (recoverCircular _).

  wpc_apply (wpc_recoverCircular with "[$]").
  iSplit.
  { iLeft in "HΦ". iModIntro. iNext. iIntros "Hcirc". iApply "HΦ".
    iExists _.
    iSplit; first by auto.
    iSplit; first by auto.
    iExists _; iFrame. }

  iIntros "!>" (γcirc' c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&Hstart&Hdisk&%&%&%)".

  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.
  iNamed "Hdiskinv".
  iDestruct (diskEnd_is_to_at_least with "[$]") as "#Hdisk_atLeast".
  (* TODO: also allocate diskEnd_txn_id ghost var and put in this thread_own_alloc *)
  iMod (thread_own_alloc with "Hdisk") as (γdiskEnd_avail_name) "(HdiskEnd_exactly&Hthread_end)".
  iDestruct (start_is_to_at_least with "[$]") as "(Hstart&#Hstart_atLeast)".
  iMod (thread_own_alloc with "Hstart") as (γstart_avail_name) "(Hstart_exactly&Hthread_start)".
  iMod (ghost_var_alloc σ.(log_state.txns)) as (γtxns_name) "(γtxns & Howntxns)".
  iMod (ghost_var_alloc diskEnd) as (γlogger_pos_name) "(γlogger_pos & Hown_logger_pos)".
  iMod (ghost_var_alloc diskEnd_txn_id) as (γlogger_txn_id) "(γlogger_txn_id & Hown_logger_txn_id)".
  iMod (ghost_var_alloc cs) as (γcs_name) "(γcs_name & Hown_cs)".
  iMod (alloc_txns_ctx _ σ.(log_state.txns)) as (γtxns_ctx_name) "Htxns_ctx".
  iMod (map_init (K:=nat) (V:=unit) ∅) as (γstable_txn_ids_name) "Hstable_txns".
  iMod (init_stable_txns _ installed_txn_id diskEnd_txn_id with "Hstable_txns")
    as "([Hstable_txns1 Hstable_txns2] & ? & ?)". iNamed.

  set (γ0 :=
         γ <| circ_name := γcirc' |>
           <| diskEnd_avail_name := γdiskEnd_avail_name |>
           <| start_avail_name := γstart_avail_name |>
           <| txns_ctx_name := γtxns_ctx_name |>
           <| cs_name := γcs_name |>
           <| logger_txn_id_name := γlogger_txn_id |>
           <| logger_pos_name := γlogger_pos_name |>
           <| txns_name := γtxns_name |>
           <| stable_txn_ids_name := γstable_txn_ids_name |>).

  set (memLog := {|
                 slidingM.log := upds;
                 slidingM.start := diskStart;
                 slidingM.mutable := int.Z diskStart + length upds |}).

  iAssert (memLog_linv_pers_core γ0 memLog diskEnd
             diskEnd_txn_id
             (* installed_txn_id_mem *)
             diskEnd_txn_id
             (* nextDiskEnd_txn_id *)
             diskEnd_txn_id
             σ.(log_state.txns)
             (* logger_pos *)
             diskEnd
             (* logger_txn_id *)
             diskEnd_txn_id
             (* installer_pos_mem *)
             installed_txn_id
             (* installer_txn_id_mem *)
             installed_txn_id) with "[-]" as "#H".
  {
    rewrite /memLog_linv_pers_core.
    iFrame "#".
    iNamed "circ.start".
    iNamed "circ.end".
    iNamed "Hdurable".
    rewrite /circ_matches_txns in Hcirc_matches. intuition idtac.
    iSplit.
    { iPureIntro.
      admit.
      (* word. *)
    }
    iDestruct (txns_ctx_txn_pos with "[$]") as "#$".
    { subst. auto with f_equal. admit. }
    assert (diskEnd = diskEnd0) by word; subst diskEnd0.
    iSplit.
    { admit. }
    iSplit.
    { eauto. }
    assert (memLog.(slidingM.mutable) = slidingM.endPos memLog) as Hmutable_is_endPos.
    { subst.
      rewrite /memLog /slidingM.endPos /=.
      word. }
    assert (memLog.(slidingM.mutable) = diskEnd) as Hmutable_is_diskEnd.
    { subst. subst memLog. simpl.
      word. }

    iSplit.
    { iDestruct (txns_ctx_txn_pos with "[$]") as "#$".
      subst; auto. admit. }

    admit.

(*

    assert (diskEnd_txn_id = (length σ.(log_state.txns) - 1)%nat) as HdiskEnd_is_last.
    { eapply wal_post_crash_durable_lb; eauto. }
    rewrite -HdiskEnd_is_last.

    iSplit.
    { iDestruct (txns_ctx_txn_pos with "[$]") as "#$".
      rewrite -Hmutable_is_endPos.
      subst; auto. }
    rewrite Hmutable_is_diskEnd.
    iSplitL "".
    { iPureIntro; lia. }
    iSplitL "".
    { rewrite /memLog_linv_txns.
      iPureIntro.
      change (memLog.(slidingM.log)) with upds.
      rewrite Hmutable_is_diskEnd.
      replace (slidingM.logIndex memLog diskEnd) with (length upds); last first.
      { rewrite /slidingM.logIndex /memLog /=.
        rewrite -Hmutable_is_diskEnd Hmutable_is_endPos.
        subst.
        rewrite /slidingM.endPos /=.
        word. }
(*
      rewrite -> (take_ge upds) by lia.
      rewrite !subslice_zero_length.
      rewrite -> (drop_ge upds) by lia.
      rewrite -> (drop_ge σ.(log_state.txns)) by lia.
      split_and!; auto using has_updates_nil.
      destruct Hdurable as [Hdurable_updates _].
      congruence.
*)
      admit.
    }
    (* replace (slidingM.memEnd memLog) with (int.Z diskStart + length upds); last first.
    { rewrite /slidingM.memEnd //=. } *)
    iPureIntro.
    replace (slidingM.memEnd memLog) with (int.Z memLog.(slidingM.mutable)); last first.
    { rewrite /memLog /slidingM.memEnd /=.
      subst; word. }
    eapply txns_mono_lt_last; eauto.
    subst; auto.
*)
  }

  wpc_frame "Hinstalled HΦ Hcirc Happender Hthread_end Hthread_start Hdurable".
  {
    crash_case.
    rewrite /is_wal_inner_durable. iExists γ0.
    iSplit; first auto.
    iSplit; first auto.
    iNext. iExists cs.
    iFrame. rewrite /disk_inv.

    iExists _, _. admit.
    (* iFrame "Hinstalled Hdurable". iFrame (Hdaddrs_init).
    iSplit.
    { iNamed "circ.start". iFrame "#%". }
    iNamed "circ.end". iFrame "#%". eauto. *)
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (ml) "Hlock".
  wp_pures.
  iDestruct (updates_slice_cap_acc with "Hupd_slice") as "[Hupd_slice Hupds_cap]".
  wp_apply (wp_mkSliding with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }

  iIntros (lslide) "Hsliding".
  iDestruct (is_sliding_wf with "[$]") as %Hsliding_wf.
  wp_apply wp_allocStruct; first by auto.
  iIntros (st) "Hwal_state".
  wp_pures.

(*
  iDestruct (memLog_linv_pers_core_strengthen γ0 with "H [] γtxns γlogger_pos γlogger_txn_id [Hstable_txns1] [] [$]") as "HmemLog_linv".
  { auto. }
  { rewrite /memLog_linv_nextDiskEnd_txn_id.
    simpl.
    iExists _; iFrame "Hstable_txns1".
    iFrame "#".
    iSplit.
    - admit. (* maybe should have fetched this txn_pos earlier for
      diskEnd_txn_id *)
    - iDestruct "Hdurable" as %Hdurable.
      destruct Hdurable.
      iPureIntro.
      intros.
      rewrite -> lookup_insert_ne by lia.
      rewrite -> lookup_singleton_ne by lia.
      auto. }
  { admit. (* new ghost variable, need to allocate fmcounter for
  installed_txn_name *) }

  iMod (alloc_lock walN _ _ (wal_linv st γ0)
          with "[$] [HmemLog_linv Hsliding Hwal_state Hstart_exactly HdiskEnd_exactly]") as "#lk".
  { rewrite /wal_linv.
    assert (int.Z diskStart + length upds = int.Z diskEnd) as Heq_plus.
    { etransitivity; last eassumption. rewrite /circΣ.diskEnd //=. subst. word. }
    iExists {| diskEnd := diskEnd; memLog := _ |}. iSplitL "Hwal_state Hsliding".
    { iExists {| memLogPtr := _; shutdown := _; nthread := _ |}.
      iDestruct (struct_fields_split with "Hwal_state") as "Hwal_state".
      iDestruct "Hwal_state" as "(?&?&?&?&_)".
      iFrame. iPureIntro. rewrite /locked_wf//=.
      { destruct Hwf_circ as (?&?). subst. split.
        * split; first lia. rewrite Heq_plus. word.
        * eauto.
      }
    }
    rewrite //= /diskEnd_linv/diskStart_linv -Heq_plus.
    iFrame. iFrame "Hdisk_atLeast Hstart_atLeast".
  }
  wp_pures.
  wp_apply (wp_newCond with "[$]").
  iIntros (condLogger) "#cond_logger".
  wp_apply (wp_newCond with "[$]").
  iIntros (condInstall) "#cond_install".
  wp_apply (wp_newCond with "[$]").
  iIntros (condShut) "#cond_shut".
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
  wp_pures.
  iNamed 1. iRight in "HΦ".
  iApply ("HΦ" $! γ0). iSplitR ""; last auto.
  rewrite /is_wal_inv_pre.
  rewrite /circular_pred.
  iSplitR "Hcirc γcs_name"; last first.
  { iExists _. iFrame. }
  rewrite /is_wal_inner. iFrame (Hwf). iFrame.
  iSplitL "".
  { rewrite /is_wal_mem.
    iExists (Build_wal_state _ _ _ _ _ _ _). simpl. iFrame "#".
  }
  iSplitL "Hstable_txns2".
  {
    rewrite /nextDiskEnd_inv.
    iExists _; iFrame.
    simpl.
    admit. (* need to construct rest of stable invariant *)
  }
  iExists _. iFrame "Hown_cs". rewrite /disk_inv. iFrame (Hdaddrs_init).
  (* When allocating stable ctx, must allocate membership facts saying that installed/diskend txn id
     are stable, then have lemma about about promoting is_installed_txn and is_durable_txn

     Lemma for promoting is_installed_read to is_installed when being_installed
     is empty, need to fix defn of latter so that the branch on if in
     being_installed is weaker in the not in case (could be either the new txn id or old, it's
     the new one only if we crashed mid install *)

  iExists _, _. iFrame "Hdurable".
  iDestruct (is_installed_restore_read with "[] [] [] Hinstalled") as "Hinstalled".
  { admit. (* fmcounter for [installed_txn_name] *) }
  { admit. (* [already_installed_name] *) }
  { admit. (* [being_installed_txns_name] *) }
  (* TODO: [is_installed] is at old durable_lb, not new [installed_txn_id], not
           sure how to resolve this (maybe [disk_inv_durable] shouldn't
           instantiate it at durable_lb but at installed_txn_id) *)
  (* TODO: [is_installed_txn], [is_durable_txn], and allocate [is_base_disk] *)
*)
  admit.
Admitted. (* BUG: the theorem statement isn't complete yet, but if we abort
this, then the proof runs in -vos mode... *)
*)

Theorem wpc_MkLog_recover stk k E1 d γ σ:
  {{{ is_wal_inner_durable γ σ dinit }}}
    MkLog #d @ stk; k; E1
  {{{ σ' γ' l, RET #l;
      ⌜relation.denote (log_crash) σ σ' tt⌝ ∗
       is_wal_inv_pre l γ' σ' dinit }}}
  {{{ ∃ γ', is_wal_inner_durable γ' σ dinit }}}.
Proof.
Admitted.

(* XXX: this is not quite correctly stated, there is some condition on E *)
Theorem is_wal_inv_alloc {k : nat} l γ σ :
  ▷ P σ -∗
  is_wal_inv_pre l γ σ dinit ={⊤}=∗
  is_wal P l γ dinit ∗
  <disc> |C={⊤}_(S k)=> (∃ σ', is_wal_inner_durable γ σ' dinit ∗ P σ').
Proof.
Admitted.

End goose_lang.
