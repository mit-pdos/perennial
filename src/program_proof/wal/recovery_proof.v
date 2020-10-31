From RecordUpdate Require Import RecordUpdate.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.
From Perennial.program_proof Require Import wal.circ_proof_crash.
From Perennial.goose_lang Require Import crash_modality.
Open Scope Z.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.
Context `{!crashG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (dinit: disk).
Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let circN := walN .@ "circ".

Lemma is_wal_inner_durable_init (bs: list Block) :
  0 d↦∗ repeat block0 513 ∗
  513 d↦∗ bs ={⊤}=∗
  let s := (log_state.mk (list_to_map (imap (λ i x, (513 + Z.of_nat i, x)) bs)) [(U64 0, [])] 0 0) in
  ∃ γ, is_wal_inner_durable γ s dinit.
Admitted.

Lemma diskEnd_is_get_at_least (γ: circ_names) q (z: Z):
  diskEnd_is γ q z ==∗ diskEnd_is γ q z ∗ diskEnd_at_least γ z.
Proof.
  iIntros "(%&Hfm&Hend)". iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
  eauto.
Qed.

Lemma start_is_get_at_least (γ: circ_names) q (z: u64):
  start_is γ q z ==∗ start_is γ q z ∗ start_at_least γ z.
Proof.
  iIntros "Hfm". by iMod (fmcounter.fmcounter_get_lb with "[$]") as "($&$)".
Qed.

Existing Instance own_into_crash.

Definition log_crash_to σ diskEnd_txn_id :=
  set log_state.durable_lb (λ _, diskEnd_txn_id)
      (set log_state.txns (take (S diskEnd_txn_id)) σ).

Lemma crash_to_diskEnd γ cs σ diskEnd_txn_id installed_txn_id :
  is_durable_txn (Σ:=Σ) γ cs σ.(log_state.txns) diskEnd_txn_id  σ.(log_state.durable_lb) -∗
  is_durable cs σ.(log_state.txns) installed_txn_id diskEnd_txn_id -∗
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

Lemma circ_matches_txns_crash cs txns installed_txn_id diskEnd_txn_id:
  circ_matches_txns cs txns installed_txn_id diskEnd_txn_id →
  circ_matches_txns cs (take (S diskEnd_txn_id) txns) installed_txn_id diskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns/has_updates.
  destruct 1 as [Heq Hlb].
  split; auto.
  intros d. rewrite Heq /subslice take_idemp //=.
Qed.

Lemma is_txn_from_take_is_txn n txns id pos:
  is_txn (take n txns) id pos →
  is_txn txns id pos.
Proof.
  rewrite /is_txn.
  rewrite ?fmap_Some.
  intros (x&Hlookup&Hpos).
  eexists; split; eauto.
  rewrite -(firstn_skipn n txns).
  apply lookup_app_l_Some; eauto.
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

  iPersist "Hdurable".
  unify_ghost_var γ.(cs_name).
  clear cs; rename cs0 into cs.
  iDestruct (is_installed_weaken_read with "Hinstalled") as (new_installed_txn_id) "Hinstalled".
  set (σ':= log_crash_to σ diskEnd_txn_id).
  iDestruct (crash_to_diskEnd with "circ.end Hdurable") as %Htrans.
  specialize (Hcrash _ Htrans).
  iNamed "circ.start".
  iNamed "circ.end".
  iDestruct "Hdurable" as %Hdurable.
  iCrash.
  iExists _; iFrame "% ∗".
  iSplit.
  { iPureIntro.
    eapply log_crash_to_wf; eauto. }
  iSplit.
  { iPureIntro.
    eapply log_crash_to_post_crash; eauto. }
  iExists cs; iFrame.
  rewrite /disk_inv_durable.
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
Proof. apply _. Qed.

Global Instance disk_inv_durable_disc γ σ cs:
  Discretizable (disk_inv_durable γ σ cs dinit).
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

Theorem wpc_mkLog_recover k (d : loc) γ σ :
  {{{ is_wal_inner_durable γ σ dinit }}}
    mkLog #d @ NotStuck; k; ⊤
  {{{ γ' l, RET #l;
       is_wal_inv_pre l γ' σ dinit ∗
       (* XXX whatever it is that background threads needs *)
       True}}}
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
    iSplit; first auto;
    iSplit; first auto;
    iFrame; iExists _; iFrame; iExists _, _; iFrame "∗ #".
  }

  iNext. iIntros (γcirc' c diskStart diskEnd bufSlice upds).
  iIntros "(Hupd_slice&Hcirc&Happender&Hstart&Hdisk&%&%&%)".

  iDestruct (is_circular_state_wf with "Hcirc") as %Hwf_circ.
  iNamed "Hdiskinv".
  iMod (diskEnd_is_get_at_least with "[$]") as "(Hdisk&#Hdisk_atLeast)".
  (* TODO: also allocate diskEnd_txn_id ghost var and put in this thread_own_alloc *)
  iMod (thread_own_alloc with "Hdisk") as (γdiskEnd_avail_name) "(HdiskEnd_exactly&Hthread_end)".
  iMod (start_is_get_at_least with "[$]") as "(Hstart&#Hstart_atLeast)".
  iMod (thread_own_alloc with "Hstart") as (γstart_avail_name) "(Hstart_exactly&Hthread_start)".
  iMod (ghost_var_alloc σ.(log_state.txns)) as (γtxns_name) "(γtxns & Howntxns)".
  iMod (ghost_var_alloc diskEnd) as (γlogger_pos_name) "(γlogger_pos & Hown_logger_pos)".
  iMod (ghost_var_alloc diskEnd_txn_id) as (γlogger_txn_id) "(γlogger_txn_id & Hown_logger_txn_id)".
  iMod (ghost_var_alloc cs) as (γcs_name) "(γcs_name & Hown_cs)".
  iMod (alloc_txns_ctx _ σ.(log_state.txns)) as (γtxns_ctx_name) "Htxns_ctx".
  iMod (map_init (K:=nat) (V:=unit) ∅) as (γstable_txn_ids_name) "Hstable_txns".
  iMod (map_alloc_ro installed_txn_id () with "Hstable_txns") as "[Hstable_txns #Hinstalled_stable]".
  { set_solver. }
  iAssert (|==> let stable_txns := <[diskEnd_txn_id:=()]> {[installed_txn_id:=()]} in
                map_ctx γstable_txn_ids_name 1 stable_txns ∗
                diskEnd_txn_id [[γstable_txn_ids_name]]↦ro ())%I
    with "[Hstable_txns]" as "HdiskEnd_txn_id_mod".
  { destruct (decide (installed_txn_id = diskEnd_txn_id)); subst.
    - iModIntro.
      rewrite insert_singleton.
      iFrame "∗#".
    - iMod (map_alloc_ro diskEnd_txn_id with "Hstable_txns") as "[Hstable_txns #HdiskEnd_stable]".
      { rewrite lookup_insert_ne //. }
      iModIntro. iFrame "#∗". }
  iMod "HdiskEnd_txn_id_mod" as
    "[[Hstable_txns1 Hstable_txns2] #HdiskEnd_stable]".

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

  iAssert (memLog_linv_pers_core γ0 memLog diskEnd diskEnd_txn_id diskEnd_txn_id σ.(log_state.txns) diskEnd diskEnd_txn_id installed_txn_id installed_txn_id installed_txn_id) with "[-]" as "#H".
  {
    rewrite /memLog_linv_pers_core.
    iFrame "#".
    iNamed "circ.start".
    iNamed "circ.end".
    iDestruct "Hdurable" as %Hdurable.
    iSplit.
    { iPureIntro.
      word. }
    iDestruct (txns_ctx_txn_pos with "[$]") as "#$".
    { subst. auto with f_equal. }
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
      subst; auto. }

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
  }

  wpc_frame "Hinstalled HΦ Hcirc Happender Hthread_end Hthread_start".
  {
    crash_case.
    rewrite /is_wal_inner_durable. iExists γ0.
    iSplit; first auto.
    iSplit; first auto.
    iNext. iExists cs.
    iFrame. rewrite /disk_inv_durable.

    iExists _, _, _. iFrame "Hinstalled Hdurable". iFrame (Hdaddrs_init).
    iSplit.
    { iNamed "circ.start". iFrame "#%". }
    iNamed "circ.end". iFrame "#%". eauto.
  }
  wp_pures.
  wp_apply (wp_new_free_lock); iIntros (ml) "Hlock".
  wp_pures.
  iDestruct (updates_slice_cap_acc with "Hupd_slice") as "[Hupd_slice Hupds_cap]".
  wp_apply (wp_mkSliding with "[$]").
  { destruct Hwf_circ as (?&?). subst; lia. }

  wp_pures.
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
