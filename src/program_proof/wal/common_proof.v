From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (γ: wal_names).

Context (P: log_state.t -> iProp Σ).

Hint Unfold slidingM.wf : word.
Hint Unfold slidingM.numMutable : word.

Lemma logIndex_set_mutable f σ pos :
  slidingM.logIndex (set slidingM.mutable f σ) pos = slidingM.logIndex σ pos.
Proof.
  rewrite /slidingM.logIndex //=.
Qed.

Theorem wp_endGroupTxn l st γ :
  {{{ is_wal P l γ ∗ wal_linv st γ }}}
    WalogState__endGroupTxn #st
  {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hlkinv) HΦ".
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  rewrite -wp_fupd.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf.
  wp_call.
  rewrite /WalogState__memEnd.
  wp_loadField. wp_apply (wp_sliding__clearMutable with "His_memLog"); iIntros "His_memLog".

  iApply "HΦ".
  iNamed "HmemLog_linv".
  iDestruct "HmemStart_txn" as "#HmemStart_txn".
  iDestruct "HmemEnd_txn" as "#HmemEnd_txn".
  iMod (txn_pos_valid_locked with "Hwal HmemEnd_txn Howntxns") as "(%HmemEnd_is_txn & Howntxns)".
  iModIntro.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf'.
  iExists (set memLog (λ _,
                       (set slidingM.mutable (λ _ : u64, slidingM.endPos σ.(memLog)) σ.(memLog))) σ).
  simpl.
  iFrame "# ∗".
  iSplitR "Howntxns HownLoggerPos_linv HnextDiskEnd".
  { iExists _; iFrame.
    iPureIntro.
    split_and!; simpl; auto; try word.
    rewrite /slidingM.endPos.
    unfold locked_wf, slidingM.wf in Hlocked_wf.
    word.
  }
  iExists memStart_txn_id, (length txns - 1)%nat, txns, _; simpl.
  iFrame "% # ∗".
  destruct_and! His_memLog.
(*
  iPureIntro; split_and!; auto; try lia.
  - pose proof (is_highest_txn_bound HdiskEnd_txn); lia.
  - pose proof (is_txn_bound _ _ _ HmemEnd_is_txn).
    replace (S (length txns - 1)) with (length txns) by lia.
    rewrite !logIndex_set_mutable.
    admit. (* TODO: invariant needs to say mem_log after mutable has appropriate
    updates (before we got this from the has_updates for the entire memLog, but
    now we need to build it from the pieces) *)
*)
Admitted.

Lemma is_txn_mid σ (a b c : nat) pos :
  wal_wf σ ->
  is_txn σ.(log_state.txns) a pos ->
  is_txn σ.(log_state.txns) c pos ->
  a ≤ b ≤ c ->
  is_txn σ.(log_state.txns) b pos.
Proof.
  rewrite /is_txn /wal_wf; intros Hwf Ha Hc Hle.
  destruct Hwf as [_ [Hwf _]].
  destruct (decide (a < b)).
  2: { assert (a = b) by lia; subst; eauto. }
  destruct (decide (b < c)).
  2: { assert (b = c) by lia; subst; eauto. }
  assert (is_Some (σ.(log_state.txns) !! b)).
  { eapply lookup_lt_is_Some_2. etransitivity.
    2: {
      eapply lookup_lt_is_Some_1.
      eapply fmap_is_Some. eauto.
    }
    lia.
  }

  destruct H as [tb Hb'].
  assert (fst <$> σ.(log_state.txns) !! b = Some (fst tb)) as Hb.
  { rewrite Hb'. reflexivity. }

  rewrite -list_lookup_fmap in Ha.
  rewrite -list_lookup_fmap in Hb.
  rewrite -list_lookup_fmap in Hc.
  rewrite -list_lookup_fmap.

  eapply Hwf in Ha as Hab'.
  1: eapply Hab' in Hb as Hab. 2: lia.
  eapply Hwf in Hb as Hbc'.
  1: eapply Hbc' in Hc as Hbc. 2: lia.
  rewrite Hb. f_equal. word.
Qed.

Lemma subslice_stable_nils γ σ (txn_id txn_id' : nat) pos :
  wal_wf σ ->
  txn_id ≤ txn_id' ->
  is_txn σ.(log_state.txns) txn_id pos ->
  is_txn σ.(log_state.txns) txn_id' pos ->
  ( nextDiskEnd_inv γ σ.(log_state.txns) ∗
    txn_id [[γ.(stable_txn_ids_name)]]↦ro () ) -∗
  ⌜Forall (λ x, snd x = nil) (subslice (S txn_id) (S txn_id') σ.(log_state.txns))⌝.
Proof.
  intros.
  iIntros "[Hinv Hstable]".
  iNamed "Hinv".
  iDestruct (map_ro_valid with "Hstablectx Hstable") as "%Hvalid".
  iPureIntro.
  apply Forall_lookup_2; intros.
  apply subslice_lookup_some in H3 as H3'.
  assert (snd <$> σ.(log_state.txns) !! (S txn_id + i)%nat = Some x.2).
  { rewrite H3'. eauto. }
  erewrite HafterNextDiskEnd in H4.
  { congruence. }
  2: eassumption.
  { lia. }
  1: eassumption.
  eapply is_txn_mid.
  1: eassumption.
  1: apply H1.
  1: apply H2.
  eapply subslice_lookup_bound' in H3 as Hbound.
  lia.
Qed.

Lemma stable_sound_alloc txns stable_txns (txn_id txn_id' : nat) (pos : u64) :
  stable_txns !! txn_id = Some () ->
  txn_id ≤ txn_id' ->
  is_txn txns txn_id pos ->
  is_txn txns txn_id' pos ->
  stable_sound txns stable_txns ->
  stable_sound txns (<[txn_id':=()]> stable_txns).
Proof.
  rewrite /stable_sound.
  intros.

  destruct (decide (txn_id' = txn_id0)).
  { subst.
    eapply (H3 txn_id txn_id'0 pos); try eassumption.
    1: lia.
    pose proof (is_txn_pos_unique _ _ _ _ H2 H6); subst.
    eauto.
  }
  eapply H3; try eassumption.
  rewrite lookup_insert_ne in H5; eauto.
Qed.

Lemma stable_sound_nils σ stable_txns txn_id txn_id' pos :
  wal_wf σ ->
  stable_txns !! txn_id = Some () ->
  is_txn σ.(log_state.txns) txn_id pos ->
  is_txn σ.(log_state.txns) txn_id' pos ->
  stable_sound σ.(log_state.txns) stable_txns ->
  Forall (λ x, x.2 = []) (subslice (S txn_id) (S txn_id') σ.(log_state.txns)).
Proof.
  intros.
  apply Forall_lookup_2; intros.
  apply subslice_lookup_some in H4 as H4'.
  assert (snd <$> σ.(log_state.txns) !! (S txn_id + i)%nat = Some x.2).
  { rewrite H4'. eauto. }
  erewrite H3 in H5.
  { congruence. }
  2: eassumption.
  { lia. }
  1: eassumption.
  eapply is_txn_mid.
  1: eassumption.
  1: apply H1.
  1: apply H2.
  eapply subslice_lookup_bound' in H4 as Hbound.
  lia.
Qed.

Theorem stable_txn_id_advance γ mutable txn_id txn_id' pos nextDiskEnd_txn_id σ :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id pos ->
  is_txn σ.(log_state.txns) txn_id' pos ->
  txn_id ≤ txn_id' ->
  memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id -∗
  nextDiskEnd_inv γ σ.(log_state.txns) -∗
  txn_id [[γ.(stable_txn_ids_name)]]↦ro () -∗
  txns_ctx γ σ.(log_state.txns)
  ==∗ (
    txn_id' [[γ.(stable_txn_ids_name)]]↦ro () ∗
    nextDiskEnd_inv γ σ.(log_state.txns) ∗
    txns_ctx γ σ.(log_state.txns) ∗
    ∃ nextDiskEnd_txn_id',
      memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id' ∗
      ⌜nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id' < length σ.(log_state.txns)⌝ ∗
      ⌜Forall (λ x, x.2 = []) (subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id') σ.(log_state.txns))⌝
  ).
Proof.
  clear P.

  iIntros (Hwf Histxn Histxn' Hle) "H0 H1 #Hstable Htxns_ctx".
  iNamed "H0".
  iNamed "H1".
  iDestruct (map_ctx_agree with "HownStableSet Hstablectx") as "%Heq". subst.
  iDestruct (map_valid with "HownStableSet Hstable") as "%Hstable".

  iDestruct (map_valid with "Hstablectx HnextDiskEnd_stable") as "%HnextDiskEnd_stable".
  iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as "%HnextDiskEnd_txn".

  destruct (stable_txns0 !! txn_id') eqn:He.
  {
    iDestruct (big_sepM_lookup with "Hstablero") as "#Hstable'"; eauto.
    iModIntro.
    iFrame "Hstable' Htxns_ctx".
    iSplitL "Hstablectx Hstablero".
    { iExists _. iFrame. iFrame "%". }
    iExists nextDiskEnd_txn_id.
    iSplitL "HownStableSet".
    { iExists _. iFrame. iFrame "#". iFrame "%". }
    rewrite subslice_zero_length.
    eapply is_txn_bound in HnextDiskEnd_txn.
    iPureIntro. intuition eauto; lia.
  }

  iCombine "HownStableSet Hstablectx" as "Hctx".
  iMod (map_alloc_ro with "Hctx") as "[Hctx #Hstable']"; eauto.
  iDestruct (big_sepM_insert with "[$Hstablero Hstable']") as "Hstablero"; eauto.
  iFrame "Hstable'".

  iModIntro.
  iDestruct "Hctx" as "[HownStableSet Hstablectx]".
  iSplitL "Hstablectx Hstablero".
  { iExists _. iFrame "Hstablectx". iFrame.
    iPureIntro. eapply stable_sound_alloc. 1: apply Hstable. all: eauto. }

  destruct (decide (txn_id' ≤ nextDiskEnd_txn_id)).
  {
    iFrame "Htxns_ctx".
    iExists nextDiskEnd_txn_id.
    iSplitL "HownStableSet".
    { iExists _. iFrame. iFrame "#".
      iPureIntro. intros.
      destruct (decide (txn_id0 = txn_id')); try lia.
      rewrite lookup_insert_ne; eauto. }
    iPureIntro.
    rewrite subslice_zero_length.
    eapply is_txn_bound in HnextDiskEnd_txn.
    intuition eauto; lia.
  }

  destruct (decide (nextDiskEnd_txn_id < txn_id)).
  {
    rewrite HnextDiskEnd_max_stable in Hstable; try lia. congruence.
  }

  assert (is_txn σ.(log_state.txns) nextDiskEnd_txn_id pos) as Hnextpos.
  {
    eapply (is_txn_mid _ txn_id _ txn_id'); eauto.
    word.
  }

  pose proof (is_txn_pos_unique _ _ _ _ HnextDiskEnd_txn Hnextpos); subst.

  iDestruct (txns_ctx_txn_pos _ _ txn_id' with "Htxns_ctx") as "#Htxn_id'_pos"; eauto.
  iFrame.
  iExists txn_id'.
  iSplit.
  { iExists _. iFrame. iFrame "Hstable'". iFrame "Htxn_id'_pos".
    iPureIntro. intros. rewrite lookup_insert_ne; last by lia.
    eapply HnextDiskEnd_max_stable. lia. }
  eapply is_txn_bound in Histxn' as Histxn'_bound.
  iPureIntro. intuition try lia.
  eapply stable_sound_nils; eauto.
Qed.

End goose_lang.
