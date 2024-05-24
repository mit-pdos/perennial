From RecordUpdate Require Import RecordSet.

From Tactical Require Import SimplMatch.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant wal.common_proof.

Section goose_lang.
Context `{!heapGS Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Hint Unfold slidingM.memEnd : word.
Hint Unfold slidingM.endPos : word.
Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Theorem wp_WalogState__updatesOverflowU64 st σ (newUpdates: u64) :
  {{{ wal_linv_fields st σ }}}
    WalogState__updatesOverflowU64 #st #newUpdates
  {{{ (overflow:bool), RET #overflow; ⌜overflow = bool_decide (slidingM.memEnd σ.(memLog) + uint.Z newUpdates >= 2^64)⌝ ∗
                                      wal_linv_fields st σ
  }}}.
Proof.
  iIntros (Φ) "Hfields HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  (* iDestruct (updates_slice_len with "His_memLog") as %HmemLog_sz. *)
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__end with "His_memLog"); iIntros "His_memLog".
  wp_apply util_proof.wp_SumOverflows.
  iIntros (?) "->".
  iApply "HΦ".
  iSplit.
  { iPureIntro.
    apply bool_decide_ext.
    word. }
  by iFrame.
Qed.

Theorem wp_WalogState__memLogHasSpace st σ (newUpdates: u64) :
  slidingM.memEnd σ.(memLog) + uint.Z newUpdates < 2^64 ->
  {{{ wal_linv_fields st σ }}}
    WalogState__memLogHasSpace #st #newUpdates
  {{{ (has_space:bool), RET #has_space; ⌜has_space = bool_decide (slidingM.memEnd σ.(memLog) - uint.Z σ.(diskEnd) + uint.Z newUpdates ≤ LogSz)⌝ ∗
                                        wal_linv_fields st σ
  }}}.
Proof.
  iIntros (Hnon_overflow Φ) "Hfields HΦ".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  (* iDestruct (updates_slice_len with "His_memLog") as %HmemLog_sz. *)
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__end with "His_memLog"); iIntros "His_memLog".
  wp_loadField.
  wp_pures.
  change (uint.Z $ word.divu (word.sub 4096 8) 8) with LogSz.
  iAssert (wal_linv_fields st σ) with "[-HΦ]" as "Hfields".
  { by iFrame. }
  wp_if_destruct; iApply "HΦ"; iFrame; iPureIntro.
  - symmetry; apply bool_decide_eq_false.
    revert Heqb; repeat word_cleanup.
  - symmetry; apply bool_decide_eq_true.
    revert Heqb; repeat word_cleanup.
Qed.

(* TODO: this intermediate function still provides no value, since it has
essentially the same spec as sliding.memWrite *)
Theorem wp_WalogState__doMemAppend l q_b memLog bufs upds :
  {{{ "His_memLog" ∷ is_sliding l q_b memLog ∗
      "Hupds" ∷ updates_slice_frag' bufs (DfracOwn 1) q_b upds ∗
      "%Hoverflow" ∷ ⌜slidingM.memEnd memLog + length upds < 2 ^ 64⌝
  }}}
    doMemAppend #l (slice_val bufs)
  {{{ RET #(slidingM.endPos (memWrite memLog upds));
      "His_memLog" ∷ is_sliding l q_b (memWrite memLog upds) }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_call.
  wp_apply (wp_sliding__memWrite with "[$His_memLog $Hupds]"); eauto.
  iIntros "His_memLog".
  wp_apply (wp_sliding__end with "[$His_memLog]").
  iIntros "His_memLog".
  wp_pures.
  iApply "HΦ".
  done.
Qed.

Lemma is_wal_wf l γ σ dinit :
  is_wal_inner l γ σ dinit -∗ ⌜wal_wf σ⌝.
Proof.
  by iNamed 1.
Qed.

Lemma memWrite_one_length_bound σ u :
  length σ.(slidingM.log) ≤
  length (memWrite_one σ u).(slidingM.log) ≤
  S (length σ.(slidingM.log)).
Proof.
  rewrite /memWrite_one.
  destruct matches; simpl; len.
Qed.

Lemma memWrite_length_bound σ upds :
  length σ.(slidingM.log) ≤
  length (memWrite σ upds).(slidingM.log) ≤
  length σ.(slidingM.log) + length upds.
Proof.
  revert σ.
  induction upds; simpl; len; intros.
  pose proof (IHupds (memWrite_one σ a)).
  pose proof (memWrite_one_length_bound σ a).
  lia.
Qed.

Lemma memWrite_memEnd_bound σ upds :
  slidingM.memEnd σ ≤
  slidingM.memEnd (memWrite σ upds) ≤
  slidingM.memEnd σ + length upds.
Proof.
  pose proof (memWrite_length_bound σ upds).
  rewrite /slidingM.memEnd.
  rewrite memWrite_same_start.
  lia.
Qed.

Lemma is_mem_memLog_endpos_highest σ txns start_txn_id upds :
  is_mem_memLog σ txns start_txn_id ->
  (forall pos txn_id, is_txn txns txn_id pos -> uint.Z pos ≤ slidingM.memEnd (memWrite σ upds)).
Proof.
  pose proof (memWrite_length_bound σ upds) as Hσ'len.
  destruct 1 as [Hupds Hhighest].
  rewrite /is_txn; intros.
  rewrite -list_lookup_fmap in H.
  apply (Forall_lookup_1 _ _ _ _ Hhighest) in H; eauto.
  rewrite /slidingM.memEnd in H |- *.
  rewrite memWrite_same_start.
  lia.
Qed.

Theorem memWrite_one_wf σ u :
  uint.Z σ.(slidingM.start) + S (length σ.(slidingM.log)) < 2^64 ->
  slidingM.wf σ ->
  slidingM.wf (memWrite_one σ u).
Proof.
  rewrite /slidingM.wf.
  intros.
  pose proof (memWrite_one_length_bound σ u).
  destruct_and!; split_and!;
              rewrite ?memWrite_one_same_mutable ?memWrite_one_same_start;
    auto; lia.
Qed.

Theorem memWrite_wf σ upds :
  uint.Z σ.(slidingM.start) + length σ.(slidingM.log) + length upds < 2^64 ->
  slidingM.wf σ ->
  slidingM.wf (memWrite σ upds).
Proof.
  rewrite /slidingM.wf.
  intros.
  pose proof (memWrite_length_bound σ upds).
  destruct_and!; split_and!;
              rewrite ?memWrite_same_mutable ?memWrite_same_start;
    auto; lia.
Qed.

Lemma set_txns_d f σ :
  (set log_state.txns f σ).(log_state.d) = σ.(log_state.d).
Proof. auto. Qed.

Lemma set_txns_installed_lb f σ :
  (set log_state.txns f σ).(log_state.installed_lb) = σ.(log_state.installed_lb).
Proof. auto. Qed.

Lemma set_txns_durable_lb f σ :
  (set log_state.txns f σ).(log_state.durable_lb) = σ.(log_state.durable_lb).
Proof. auto. Qed.

Lemma locked_wf_memWrite σ upds :
  slidingM.wf (memWrite σ.(memLog) upds) ->
  locked_wf σ ->
  locked_wf (set memLog (λ _, memWrite σ.(memLog) upds) σ).
Proof.
  rewrite /locked_wf; intros.
  rewrite !memWrite_same_mutable !memWrite_same_start.
  destruct_and!; split_and!; auto.
Qed.

Lemma is_mem_memLog_append (bs : list update.t) (σ : locked_state) (σs : log_state.t) (memStart_txn_id : nat) :
    slidingM.wf (memWrite σ.(memLog) bs) →
    (S memStart_txn_id ≤ length σs.(log_state.txns))%nat →
    is_mem_memLog σ.(memLog) σs.(log_state.txns) memStart_txn_id →
    is_mem_memLog (memWrite σ.(memLog) bs)
                    (σs.(log_state.txns) ++ [(slidingM.endPos (memWrite σ.(memLog) bs), bs)])
                    memStart_txn_id.
Proof.
  intros Hwf HmemStart_bound.
  rewrite /is_mem_memLog /has_updates.
  intros [Hupdates Hpos_bound].
  split.
  - intros.
    rewrite -> drop_app_le by auto.
    rewrite txn_upds_app.
    rewrite memWrite_apply_upds.
    rewrite !apply_upds_app.
    simpl.
    rewrite Hupdates //.
  - rewrite fmap_app.
    apply Forall_app; split.
    + eapply Forall_impl; eauto.
      simpl; intros.
      pose proof (memWrite_memEnd_bound σ.(memLog) bs).
      word.
    + apply Forall_singleton.
      rewrite slidingM.memEnd_ok; auto.
      lia.
Qed.

Hint Rewrite memWrite_one_same_start memWrite_one_same_mutable : sliding.
Hint Rewrite memWrite_same_start memWrite_same_mutable : sliding.

Ltac sliding := autorewrite with sliding; try done.

Definition numMutableN (memLog: slidingM.t): nat :=
  (uint.nat memLog.(slidingM.mutable) - uint.nat memLog.(slidingM.start))%nat.

Theorem memWrite_one_same_numMutableN memLog u :
  numMutableN (memWrite_one memLog u) = numMutableN memLog.
Proof.
  rewrite /numMutableN; sliding.
Qed.

Theorem memWrite_same_numMutableN memLog upds :
  numMutableN (memWrite memLog upds) = numMutableN memLog.
Proof.
  rewrite /numMutableN; sliding.
Qed.

Lemma memWrite_one_preserves_mutable memLog u :
  slidingM.wf memLog →
  take (numMutableN (memWrite_one memLog u)) (memWrite_one memLog u).(slidingM.log) =
  take (numMutableN memLog) memLog.(slidingM.log).
Proof.
  intros Hwf.
  rewrite /memWrite_one /numMutableN.
  destruct matches; simpl.
  - rewrite -> take_insert by lia; auto.
  - rewrite -> take_app_le by word; auto.
  - rewrite -> take_app_le by word; auto.
Qed.

Lemma memWrite_preserves_mutable' memLog upds :
  slidingM.wf memLog ->
  uint.Z memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  take
    (numMutableN (memWrite memLog upds))
    (memWrite memLog upds).(slidingM.log) =
  take
    (numMutableN memLog)
    memLog.(slidingM.log).
Proof.
  intros Hwf Hoverflow.
  generalize dependent memLog.
  induction upds; simpl; auto; intros.
  rewrite IHupds; sliding.
  - rewrite memWrite_one_preserves_mutable; auto.
  - eapply memWrite_one_wf; eauto; try lia.
  - pose proof (memWrite_one_length_bound memLog a); lia.
Qed.

Lemma memWrite_preserves_mutable memLog upds (n : nat) :
  slidingM.wf memLog ->
  n ≤ numMutableN memLog ->
  uint.Z memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  take
    n
    (memWrite memLog upds).(slidingM.log) =
  take
    n
    memLog.(slidingM.log).
Proof.
  intros Hwf Hn Hoverflow.
  pose proof (memWrite_preserves_mutable' memLog upds Hwf Hoverflow) as Hwf'.
  rewrite memWrite_same_numMutableN in Hwf'.
  replace n with (n `min` numMutableN memLog)%nat by lia.
  repeat rewrite <- firstn_firstn.
  rewrite Hwf'. eauto.
Qed.

Lemma memWrite_preserves_mutable_suffix memLog upds diskEnd (mutableEnd : u64) :
  slidingM.wf memLog ->
  uint.Z mutableEnd ≤ uint.Z memLog.(slidingM.mutable) ->
  uint.Z memLog.(slidingM.start) + length memLog.(slidingM.log) + length upds < 2^64 ->
  subslice (slidingM.logIndex memLog diskEnd)
           (slidingM.logIndex memLog mutableEnd)
           (memWrite memLog upds).(slidingM.log) =
  subslice (slidingM.logIndex memLog diskEnd)
           (slidingM.logIndex memLog mutableEnd)
           memLog.(slidingM.log).
Proof.
  intros Hwf Hn Hoverflow.
  rewrite /subslice.
  rewrite memWrite_preserves_mutable; auto.
  rewrite /numMutableN /slidingM.logIndex. word.
Qed.

Lemma numMutableN_ok memLog :
  slidingM.wf memLog ->
  uint.nat (slidingM.numMutable memLog) = numMutableN memLog.
Proof.
  rewrite /numMutableN; intros; word.
Qed.

Lemma is_installed_append γ d txns txns' txn_id installer_txn_id diskEnd_txn_id :
  is_installed γ d txns txn_id installer_txn_id diskEnd_txn_id -∗
  is_installed γ d (txns ++ txns') txn_id installer_txn_id diskEnd_txn_id.
Proof.
  rewrite /is_installed /is_installed_core.
  iNamed 1. iNamed "Howninstalled".
  iExists already_installed.
  iFrame.
  rewrite -subslice_before_app_eq; last by lia. iFrame "#".
  iSplitR "Hdata".
  - iPureIntro.
    len.
  - iApply (big_sepM_mono with "Hdata"); simpl.
    iIntros (k x Hkx) "H".
    iDestruct "H" as (b txn_id') "(% & H & %)".
    iExists b, txn_id'. iFrame. iFrame "%". iPureIntro.
    split; first by lia.
    intuition; rewrite take_app_le //; lia.
Qed.

Lemma is_durable_append γ cs txns txns' installed_txn_id installer_txn_id diskEnd_txn_id :
  (diskEnd_txn_id < length txns)%nat ->
  is_durable γ cs txns installed_txn_id installer_txn_id diskEnd_txn_id -∗
  is_durable (Σ:=Σ) γ cs (txns ++ txns') installed_txn_id installer_txn_id diskEnd_txn_id.
Proof.
  intros Hbound.
  rewrite /is_durable; iNamed 1.
  iExists _, _, _.
  iFrame.
  iPureIntro.
  split; last by lia.
  apply is_memLog_boundaries_append_txns.
  assumption.
Qed.

Lemma is_txn_app txns extra txn_id pos :
  is_txn txns txn_id pos ->
  is_txn (txns ++ extra) txn_id pos.
Proof.
  rewrite /is_txn; intros.
  destruct (txns !! txn_id) eqn:He.
  2: { simpl in H. congruence. }
  eapply (lookup_app_l_Some _ extra) in He.
  rewrite He. eauto.
Qed.

Theorem disk_inv_append γ σs cs dinit pos upds :
  disk_inv γ σs cs dinit -∗
  disk_inv γ (set log_state.txns (λ txns, txns ++ [(pos, upds)]) σs) cs dinit.
Proof.
  rewrite /disk_inv; iNamed 1; simpl.
  iExists installed_txn_id, installer_txn_id, diskEnd_txn_id; iFrame.
  iNamed "circ.start".
  iNamed "circ.end".
  iSplitL "Hinstalled".
  { iApply (is_installed_append with "[$]"). }
  iSplitL "Hdurable".
  { iApply (is_durable_append with "[$]").
    eapply is_txn_bound; eauto. }
  iSplit.
  { iFrame "#". iFrame "%". iPureIntro. eapply is_txn_app. eauto. }
  iSplit.
  {
    iExists _.
    iFrame "#".
    iExists _.
    iFrame "%".
    iPureIntro.
    rewrite app_length subslice_app_1; last by lia.
    split; first by lia.
    split; first by assumption.
    split.
    - eapply is_txn_app.
      assumption.
    - eapply is_txn_app.
      assumption.
  }
  iFrame "#".
  done.
Qed.

Lemma memWrite_one_preserves_logIndex σ upd pos :
  slidingM.logIndex (memWrite_one σ upd) pos =
  slidingM.logIndex σ pos.
Proof.
  rewrite /slidingM.logIndex.
  rewrite memWrite_one_same_start //.
Qed.

Lemma memWrite_preserves_logIndex σ upds pos :
  slidingM.logIndex (memWrite σ upds) pos =
  slidingM.logIndex σ pos.
Proof.
  rewrite /slidingM.logIndex.
  rewrite memWrite_same_start //.
Qed.

Lemma memWrite_one_endPos σ u :
  slidingM.wf σ ->
  slidingM.memEnd σ + 1 < 2 ^ 64 ->
  uint.Z σ.(slidingM.mutable) < uint.Z (slidingM.endPos (memWrite_one σ u)).
Proof.
  rewrite /slidingM.wf /slidingM.memEnd; intros.
  rewrite /memWrite_one.
  destruct (find_highest_index (update.addr <$> σ.(slidingM.log)) u.(update.addr)) eqn:He.
  - destruct (decide (uint.Z σ.(slidingM.mutable) - uint.Z σ.(slidingM.start) ≤ n)).
    + rewrite /slidingM.endPos /set insert_length /=.
      assert (uint.Z σ.(slidingM.mutable) ≤ uint.Z σ.(slidingM.start) + length σ.(slidingM.log)) by word.
      assert (uint.Z σ.(slidingM.mutable) ≤ uint.Z σ.(slidingM.start) + n) by word.
      assert (n < length σ.(slidingM.log)).
      2: { word. }
      eapply find_highest_index_ok' in He. intuition idtac.
      eapply lookup_lt_Some in H.
      rewrite fmap_length in H. lia.
    + rewrite /slidingM.endPos /set app_length /=. word.
  - rewrite /slidingM.endPos /set app_length /=. word.
Qed.

Lemma memWrite_endPos :
  ∀ bs σ,
    slidingM.wf σ ->
    slidingM.memEnd σ + length bs < 2 ^ 64 ->
    uint.Z (slidingM.endPos σ) ≤ uint.Z (slidingM.endPos (memWrite σ bs)).
Proof.
  rewrite /slidingM.memEnd.
  induction bs.
  - simpl. lia.
  - simpl. intros.
    etransitivity.
    2: { eapply IHbs; eauto.
      { eapply memWrite_one_wf; eauto. word. }
      pose proof (memWrite_one_length_bound σ a).
      rewrite memWrite_one_same_start. word.
    }

    rewrite /slidingM.endPos.
    pose proof (memWrite_one_length_bound σ a).
    rewrite memWrite_one_same_start. word.
Qed.

Lemma memWrite_endPos_lt bs σ :
  slidingM.wf σ ->
  slidingM.memEnd σ + length bs < 2 ^ 64 ->
  0 < length bs ->
  uint.Z σ.(slidingM.mutable) < uint.Z (slidingM.endPos (memWrite σ bs)).
Proof.
  destruct bs; simpl; intros; try lia.
  eapply Z.lt_le_trans.
  2: {
    eapply memWrite_endPos.
    { eapply memWrite_one_wf; eauto. word. }
    unfold slidingM.memEnd in *.
    pose proof (memWrite_one_length_bound σ t).
    rewrite memWrite_one_same_start. word.
  }

  eapply memWrite_one_endPos; eauto.
  lia.
Qed.

Lemma stable_sound_app σ (stable_txns : gmap nat ()) bs memStart_txn_id nextDiskEnd_txn_id ml :
  wal_wf σ ->
  slidingM.wf ml ->
  slidingM.memEnd ml + length bs < 2 ^ 64 ->
  is_mem_memLog ml σ.(log_state.txns) memStart_txn_id ->
  is_txn σ.(log_state.txns) nextDiskEnd_txn_id ml.(slidingM.mutable) ->
  ( ∀ (txn_id : nat), txn_id > nextDiskEnd_txn_id → stable_txns !! txn_id = None ) ->
  stable_sound σ.(log_state.txns) stable_txns ->
  stable_sound (σ.(log_state.txns) ++ [(slidingM.endPos (memWrite ml bs), bs)]) stable_txns.
Proof.
  rewrite /stable_sound.
  intros Hwalwf Hwf Hbound HismemLog Histxn Hmaxstable Hsound.
  intros.

  destruct (decide (txn_id < length σ.(log_state.txns))).
  2: {
    rewrite Hmaxstable in H0; first by congruence.
    pose proof (is_txn_bound _ _ _ Histxn). lia.
  }

  destruct (decide (txn_id' < length σ.(log_state.txns))).
  {
    rewrite -> lookup_app_l by lia.
    rewrite /is_txn lookup_app_l in H1; last by lia.
    rewrite /is_txn lookup_app_l in H2; last by lia.
    eapply Hsound; eauto.
  }

  destruct (decide (txn_id' = length σ.(log_state.txns))); subst.
  2: {
    rewrite /is_txn in H2.
    rewrite lookup_ge_None_2 in H2.
    { simpl in *; congruence. }
    rewrite app_length /=. lia.
  }

  rewrite lookup_app_r; last by lia.
  replace (length σ.(log_state.txns) - length σ.(log_state.txns))%nat with 0%nat by lia.
  simpl.

  rewrite /is_txn lookup_app_r in H2; last by lia.
  replace (length σ.(log_state.txns) - length σ.(log_state.txns))%nat with 0%nat in H2 by lia.
  simpl in H2. inversion H2; clear H2; subst.

  rewrite /is_txn lookup_app_l in H1; last by lia.

  destruct (decide (length bs = 0)%nat).
  { destruct bs; eauto; simpl in *; lia. }

  assert (uint.Z ml.(slidingM.mutable) < uint.Z (slidingM.endPos (memWrite ml bs))).
  { eapply memWrite_endPos_lt; eauto. lia. }

  destruct (decide (txn_id > nextDiskEnd_txn_id)).
  { rewrite Hmaxstable in H0; first by congruence. lia. }

  assert (uint.Z (slidingM.endPos (memWrite ml bs)) ≤ uint.Z ml.(slidingM.mutable)).
  2: lia.

  eapply wal_wf_txns_mono_pos'.
  1: eauto.
  1: eauto.
  1: eauto.
  lia.
Qed.

Lemma memWrite_one_eq ml addr b d :
  slidingM.wf ml ->
  apply_upds
    (drop (slidingM.logIndex ml ml.(slidingM.mutable))
      (memWrite_one ml {| update.addr := addr; update.b := b |}).(slidingM.log)) d !! uint.Z addr = Some b.
Proof.
  rewrite /slidingM.wf; intros.
  rewrite /memWrite_one /=.
  destruct (find_highest_index (update.addr <$> ml.(slidingM.log)) addr) eqn:Hidx; rewrite Hidx /=.
  - destruct (decide (uint.Z ml.(slidingM.mutable) - uint.Z ml.(slidingM.start) ≤ n)); simpl.
    + eapply find_highest_index_Some_split in Hidx.
      destruct Hidx as [l1 [l2 Hidx]].
      destruct Hidx as [Happ [Hhighest Hlen]].
      eapply fmap_app_inv in Happ.
      destruct Happ as [x1 [x2 Happ]].
      destruct Happ as [Hx1 [Hx2 Happ]].
      rewrite Happ.
      symmetry in Hx2.
      eapply fmap_cons_inv in Hx2.
      destruct Hx2 as [x [x3 Hx3]].
      destruct Hx3 as [Haddr [Hl2 Hx2]]. subst.
      rewrite -> fmap_length in *. replace (length x1) with (length x1 + 0)%nat by lia.
      rewrite insert_app_r.
      simpl.
      rewrite drop_app_le.
      2: { rewrite /slidingM.logIndex. lia. }
      rewrite apply_upds_app /=.
      rewrite apply_upds_lookup_insert_highest; eauto.
    + rewrite drop_app_le.
      2: { rewrite /slidingM.logIndex. word. }
      rewrite apply_upds_app /=.
      rewrite lookup_insert; done.
  - rewrite drop_app_le.
    2: { rewrite /slidingM.logIndex. word. }
    rewrite apply_upds_app /=.
    rewrite lookup_insert; done.
Qed.

Lemma apply_upds_lookup_eq : ∀ upds d0 d1 a,
  d0 !! a = d1 !! a ->
  apply_upds upds d0 !! a = apply_upds upds d1 !! a.
Proof.
  induction upds; simpl; intros; eauto.
  destruct a.
  destruct (decide (a0 = uint.Z addr)); subst.
  - eapply IHupds. rewrite !lookup_insert. eauto.
  - eapply IHupds. rewrite lookup_insert_ne; eauto. rewrite lookup_insert_ne; eauto.
Qed.

Lemma memWrite_one_ne ml addr a' b d :
  slidingM.wf ml ->
  a' ≠ uint.Z addr ->
  apply_upds
    (drop (slidingM.logIndex ml ml.(slidingM.mutable))
      (memWrite_one ml {| update.addr := addr; update.b := b |}).(slidingM.log)) d !! a' =
  apply_upds
    (drop (slidingM.logIndex ml ml.(slidingM.mutable))
      ml.(slidingM.log)) d !! a'.
Proof.
  rewrite /slidingM.wf; intros.
  rewrite /memWrite_one /=.
  destruct (find_highest_index (update.addr <$> ml.(slidingM.log)) addr) eqn:Hidx; rewrite Hidx /=.
  - destruct (decide (uint.Z ml.(slidingM.mutable) - uint.Z ml.(slidingM.start) ≤ n)); simpl.
    + eapply find_highest_index_Some_split in Hidx.
      destruct Hidx as [l1 [l2 Hidx]].
      destruct Hidx as [Happ [Hhighest Hlen]].
      eapply fmap_app_inv in Happ.
      destruct Happ as [x1 [x2 Happ]].
      destruct Happ as [Hx1 [Hx2 Happ]].
      rewrite Happ.
      symmetry in Hx2.
      eapply fmap_cons_inv in Hx2.
      destruct Hx2 as [x [x3 Hx3]].
      destruct Hx3 as [Haddr [Hl2 Hx2]]. subst.
      rewrite -> fmap_length in *. replace (length x1) with (length x1 + 0)%nat by lia.
      rewrite insert_app_r. destruct x.
      simpl.
      rewrite !drop_app_le.
      2: { rewrite /slidingM.logIndex. lia. }
      2: { rewrite /slidingM.logIndex. lia. }
      rewrite !apply_upds_app /=.
      eapply apply_upds_lookup_eq.
      rewrite lookup_insert_ne.
      2: { simpl in H0. congruence. }
      rewrite lookup_insert_ne.
      2: { simpl in H0. congruence. }
      done.
    + rewrite drop_app_le.
      2: { rewrite /slidingM.logIndex. word. }
      rewrite apply_upds_app /=.
      rewrite lookup_insert_ne; done.
  - rewrite drop_app_le.
    2: { rewrite /slidingM.logIndex. word. }
    rewrite apply_upds_app /=.
    rewrite lookup_insert_ne; done.
Qed.

Lemma memWrite_has_updates ml txns bs :
  slidingM.wf ml ->
  slidingM.memEnd ml + length bs < 2 ^ 64 ->
  has_updates (drop (slidingM.logIndex ml ml.(slidingM.mutable)) ml.(slidingM.log))
              (txns) ->
  has_updates (drop (slidingM.logIndex (memWrite ml bs) (memWrite ml bs).(slidingM.mutable)) (memWrite ml bs).(slidingM.log))
              (txns ++ [(slidingM.endPos (memWrite ml bs), bs)]).
Proof.
  rewrite /has_updates.
  intros Hwf Hoverflow Hp d.
  rewrite txn_upds_app.
  rewrite apply_upds_app /=.
  rewrite -Hp; clear Hp.
  rewrite /txn_upds /=. rewrite app_nil_r.

  generalize dependent ml.
  induction bs; simpl; intros; eauto.

  rewrite IHbs; clear IHbs.
  2: {
    eapply memWrite_one_wf; eauto.
    rewrite /slidingM.memEnd in Hoverflow. lia.
  }
  2: {
    pose proof (memWrite_one_length_bound ml a).
    rewrite /slidingM.memEnd.
    rewrite memWrite_one_same_start.
    word.
  }

  f_equal.
  rewrite memWrite_one_preserves_logIndex.
  rewrite memWrite_one_same_mutable.
  destruct a.
  eapply map_eq; intros.
  destruct (decide (i = uint.Z addr)); subst.
  {
    rewrite lookup_insert.
    rewrite memWrite_one_eq; eauto.
  }
  {
    rewrite lookup_insert_ne; eauto.
    rewrite memWrite_one_ne; eauto.
  }
Qed.

Theorem wp_Walog__MemAppend (PreQ : iProp Σ) (Q: u64 -> iProp Σ) l γ dinit bufs bs :
  {{{ is_wal P l γ dinit ∗
       updates_slice bufs bs ∗
       (∀ σ σ' pos,
         ⌜wal_wf σ⌝ -∗
         ⌜relation.denote (log_mem_append bs) σ σ' pos⌝ -∗
         let txn_id := length σ.(log_state.txns) in
         (P σ -∗ |NC={⊤ ∖↑ N}=> ⌜addrs_wf bs σ.(log_state.d)⌝ ∗ P σ' ∗ (txn_pos γ txn_id pos -∗ Q pos))) ∧ PreQ
   }}}
    Walog__MemAppend #l (slice_val bufs)
  {{{ pos (ok : bool), RET (#pos, #ok); if ok then Q pos ∗ ∃ txn_id, txn_pos γ txn_id pos else PreQ }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hbufs & Hfupd) HΦ".
  wp_call.
  iDestruct (updates_slice_to_frag with "Hbufs") as "Hbufs".
  iDestruct (updates_slice_frag_len with "Hbufs") as %Hbufs_sz.
  wp_apply wp_slice_len.
  wp_pures.
  change (uint.Z (word.divu (word.sub 4096 8) 8)) with LogSz.
  wp_if_destruct.
  - wp_pures.
    iApply "HΦ".
    by iDestruct "Hfupd" as "[_ $]".
  - wp_apply wp_ref_to; [ by val_ty | iIntros (txn_l) "txn" ].
    wp_apply wp_ref_to; [ by val_ty | iIntros (ok_l) "ok" ].
    iMod (is_wal_read_mem with "Hwal") as "#Hmem".
    wp_pures.
    iNamed "Hmem".
    iNamed "Hstfields".
    wp_loadField.
    wp_apply (acquire_spec with "lk"); iIntros "(Hlocked&Hlockinv)".
    wp_loadField.
    wp_pures.
    wp_bind (For _ _ _).
    wp_apply (wp_forBreak_cond
                (fun b =>
                   ∃ (txn: u64) (ok: bool),
                     "txn" ∷ txn_l ↦[uint64T] #txn ∗
                     "ok" ∷ ok_l ↦[boolT] #ok ∗
                     "%Hok_is" ∷ ⌜if b then ok = true else True⌝ ∗
                    "Hsim" ∷ (if b then
                               (∀ (σ σ' : log_state.t) pos,
                                ⌜wal_wf σ⌝
                                -∗ ⌜relation.denote (log_mem_append bs) σ σ' pos⌝
                                -∗ P σ
                                -∗ |NC={⊤ ∖ ↑N}=> ⌜addrs_wf bs σ.(log_state.d)⌝ ∗ P σ'
                                ∗ (txn_pos γ (length σ.(log_state.txns)) pos
                                -∗ Q pos)) ∧ PreQ else
                               (if ok then Q txn ∗ ∃ txn_id, txn_pos γ txn_id txn else PreQ)) ∗
                     "Hlocked" ∷ locked #σₛ.(memLock) ∗
                     "Hlockinv" ∷ wal_linv σₛ.(wal_st) γ ∗
                     "Hbufs" ∷ if b then updates_slice_frag bufs (DfracOwn 1) bs else emp
                )%I
                with  "[] [-HΦ]"
             ).
    2: { iExists _, _; iFrame. auto. }
    { clear Φ.
      iIntros "!>" (Φ) "HI HΦ". iNamed "HI".
      wp_pures.
      intuition subst.
      (* hide postcondition from the IPM goal *)
      match goal with
      | |- context[Esnoc _ (INamed "HΦ") ?P] =>
        set (post:=P)
      end.
      wp_apply wp_slice_len.
      iNamed "Hlockinv".
      wp_apply (wp_WalogState__updatesOverflowU64 with "Hfields").
      iIntros (?) "[-> Hfields]".
      wp_pures.
      wp_if_destruct.
      { (* error path *)
        wp_store.
        iApply "HΦ".
        iExists _, _; iFrame.
        by iDestruct "Hsim" as "[_ $]". }
      wp_apply wp_slice_len.
      wp_apply (wp_WalogState__memLogHasSpace with "Hfields").
      { revert Heqb0; word. }
      iIntros (?) "[-> Hfields]".
      wp_if_destruct.
      - iNamed "Hfields". iNamed "Hfield_ptsto".
        wp_loadField.
        wp_apply (wp_WalogState__doMemAppend with "[$His_memLog $Hbufs]").
        { rewrite -Hbufs_sz. iPureIntro. word. }
        assert (slidingM.wf σ.(memLog)).
        { destruct Hlocked_wf; auto. }
        set (memLog' := memWrite σ.(memLog) bs).
        assert (slidingM.wf memLog').
        { subst memLog'.
          apply memWrite_wf; [ word | auto ]. }
        iNamed 1.
        iDestruct "Hwal" as "[Hwal Hcirc]".
        rewrite -wp_fupd.
        wp_store.
        wp_bind Skip.
        iInv "Hwal" as (σs) "[Hinner HP]".
        wp_call.
        iDestruct (is_wal_wf with "Hinner") as %Hwal_wf.
        iDestruct "Hsim" as "[Hsim _]".
        iNamed "HmemLog_linv".
        iNamed "HnextDiskEnd".
        iNamed "Hinner".
        iNamed "Hlinv_pers".
        (* XXX: unify_ghost doesn't rewrite everywhere *)
        iDestruct (ghost_var_agree with "γtxns Howntxns") as %Htxnseq; subst.
        iDestruct (txn_pos_valid_general with "Htxns_ctx HmemStart_txn") as %HmemStart_txn.
        iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as %HnextDiskEnd_txn.
        iMod (fupd_mask_subseteq (⊤ ∖ ↑N)) as "HinnerN"; first by solve_ndisj.
        unshelve (
          epose proof (
            memLog_linv_txns_to_is_mem_memLog _ _ _ _ _ _ _ _ _ _ _ Htxns
          )
        ); eauto.
        iMod ("Hsim" $! _ (set log_state.txns (λ txns, txns ++ [(slidingM.endPos memLog', bs)]) σs)
                with "[% //] [%] [$HP]") as "(%Haddrs & HP & HQ)".
        { simpl; monad_simpl.
          eexists _ (slidingM.endPos memLog'); simpl; monad_simpl.
          econstructor; eauto.
          destruct Hlocked_wf.
          rewrite slidingM.memEnd_ok; eauto.
          eapply is_mem_memLog_endpos_highest; eauto. }
        iMod "HinnerN" as "_".
        iMod (ghost_var_update_halves (σs.(log_state.txns) ++ [(slidingM.endPos memLog', bs)])
                with "γtxns Howntxns") as "[γtxns Howntxns]".
        iMod (alloc_txn_pos (slidingM.endPos memLog') bs with "Htxns_ctx") as "[Htxns_ctx #Hnew_txn]".
        iDestruct (txn_val_to_pos with "Hnew_txn") as "Hnew_txn_pos".
        iSpecialize ("HQ" with "Hnew_txn_pos").

        iNamed "HnextDiskEnd_inv".
        iDestruct (map_ctx_agree with "Hstablectx HownStableSet") as %->.

        iModIntro.
        iSplitL "Hstablectx Hstablero Hdisk Hmem HP γtxns Htxns_ctx".

        (* re-prove invariant *)
        {
          iNext.
          iExists _; iFrame "HP".
          iFrame.
          iSplit; [ iPureIntro | ].
          { eapply mem_append_preserves_wf; eauto.
            rewrite slidingM.memEnd_ok; eauto.
            eapply is_mem_memLog_endpos_highest; eauto. }
          simpl.
          iSplitR.
          {
            iPureIntro.
            eapply stable_sound_app; eauto. word.
          }
          iDestruct "Hdisk" as (cs) "Hdisk".
          iNamed "Hdisk".
          iExists cs; iFrame.
          iApply (disk_inv_append with "Hdisk").
        }

        (* continue and prove loop invariant (lock invariant mostly) *)
        wp_pures.
        iModIntro.
        iApply "HΦ".
        iFrame "ok txn HQ Hlocked".
        iSplit.
        { iExists _; iFrame "#". }
        rewrite (right_id _ bi_sep).
        iExists (set memLog (λ _, memLog') σ); simpl.
        rewrite /wal_linv_core memWrite_same_start.
        iFrame "HdiskEnd_circ Hstart_circ HownDiskEndMem_linv HownDiskEndMemTxn_linv".
        iSplitR "HmemStart_txn HnextDiskEnd_txn Howntxns HownStableSet
                 HownLoggerPos_linv HownLoggerTxn_linv
                 HownInstallerPosMem_linv HownInstallerTxnMem_linv
                 HownInstalledPosMem_linv HownInstalledTxnMem_linv".
        { iExists _; iFrame.
          iPureIntro.
          eapply locked_wf_memWrite; eauto. }
        iExists _, nextDiskEnd_txn_id, _, _, _, _, _; iFrame.
        rewrite memWrite_same_start memWrite_same_mutable; iFrame "#".
        autorewrite with len.
        iFrame.
        iFrame "%".
        subst memLog'.
        rewrite Nat.add_sub memWrite_same_start memWrite_same_mutable /=.
        iSplit.
        1: iPureIntro; lia.
        iFrame "HmemStart_txn Hnew_txn_pos".
        iSplit.
        {
          iPureIntro.
          rewrite /is_txn lookup_app_l.
          2: apply is_txn_bound in HdiskEnd_txn; assumption.
          eauto.
        }
        iSplit.
        {
          iPureIntro.
          apply memLog_linv_txns_memWrite.
          assumption.
        }
        iPureIntro.
        split; last by lia.
        rewrite fmap_app.
        eapply Forall_app; split.
        { pose proof (memWrite_memEnd_bound σ.(memLog) bs).
          eapply Forall_impl; eauto. simpl. intros. lia. }
        simpl. econstructor; eauto. word.
      - wp_apply util_proof.wp_DPrintf.
        iAssert (wal_linv σₛ.(wal_st) γ) with "[Hfields HmemLog_linv HdiskEnd_circ Hstart_circ]" as "Hlockinv".
        { iExists _; iFrame. }
        wp_apply (wp_endGroupTxn with "Hlockinv").
        iIntros "Hlockinv".
        wp_loadField.
        wp_apply (wp_condBroadcast with "[$cond_logger]").
        wp_loadField.
        wp_apply (wp_condWait with "[$cond_logger $Hlocked $lk $Hlockinv]").
        iIntros "(Hlocked&Hlockinv)".
        wp_pures.
        iApply "HΦ".
        iExists _, _; by iFrame. }
    iNamed 1.
    wp_loadField.
    wp_apply (release_spec with "[$lk $Hlocked $Hlockinv]").
    wp_pures.
    wp_load. wp_load.
    wp_pures.
    iApply "HΦ".
    destruct ok; by iFrame.
Qed.

End goose_lang.
