From RecordUpdate Require Import RecordSet.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Section goose_lang.
Context `{!heapGS Σ}.
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

Lemma stable_alloc_end γ txns mutable nextDiskEnd_txn_id endpos :
  ( memLog_linv_nextDiskEnd_txn_id γ mutable nextDiskEnd_txn_id ∗
    nextDiskEnd_inv γ txns ∗
    txns_ctx γ txns ∗
    txn_pos γ (length txns - 1) endpos
  )
  ==∗
  (
    memLog_linv_nextDiskEnd_txn_id γ endpos (length txns - 1) ∗
    nextDiskEnd_inv γ txns ∗
    txns_ctx γ txns ∗
    (length txns - 1)%nat [[γ.(stable_txn_ids_name)]]↦ro tt
  ).
Proof.
  iIntros "(H0 & H1 & Htxns_ctx & #Hend)".
  iNamed "H1".
  iNamed "H0".
  iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as "%HnextDiskEnd_txn".
  eapply is_txn_bound in HnextDiskEnd_txn as HnextDiskEnd_bound.
  iDestruct (map_ctx_agree with "HownStableSet Hstablectx") as %->.
  iCombine "HownStableSet Hstablectx" as "Hstablectx".
  destruct (stable_txns !! (length txns - 1)%nat) eqn:He.
  {
    iDestruct (big_sepM_lookup with "Hstablero") as "#Hstable"; eauto.
    iModIntro.
    iDestruct "Hstablectx" as "[Hstablectx HownStableSet]".
    iFrame "Htxns_ctx Hstable".
    iSplitL "HownStableSet".
    { iExists _. iFrame. iFrame "# %".
      iPureIntro. intros. eapply HnextDiskEnd_max_stable. lia. }
    iExists _. iFrame. iFrame "%".
  }

  iMod (map_alloc_ro with "Hstablectx") as "[Hstablectx #Hstable]"; eauto.
  iDestruct (big_sepM_insert with "[$Hstablero $Hstable]") as "Hstablero"; eauto.
  iModIntro.
  iDestruct "Hstablectx" as "[Hstablectx HownStableSet]".
  iFrame "Htxns_ctx Hstable".
  iSplitL "HownStableSet".
  { iExists _. iFrame. iFrame "# %".
    iPureIntro. intros. rewrite lookup_insert_ne; try lia. eapply HnextDiskEnd_max_stable. lia. }
  iExists _. iFrame.
  iPureIntro. rewrite /stable_sound. intros.
  destruct (decide (txn_id = (length txns - 1)%nat)); subst.
  { eapply is_txn_bound in H2. lia. }
  rewrite lookup_insert_ne in H0; eauto.
Qed.

Theorem wp_sliding__clearMutable_wal l st γ dinit σ :
  {{{ is_wal P l γ dinit ∗ wal_linv_core st γ σ }}}
    sliding__clearMutable (struct.loadF WalogState "memLog" #st)
  {{{ σ', RET #();
    wal_linv_core st γ σ' ∗
    ⌜length σ.(memLog).(slidingM.log) = length σ'.(memLog).(slidingM.log)⌝
  }}}.
Proof.
  iIntros (Φ) "(#Hwal & Hlkinv) HΦ".
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  rewrite -wp_ncfupd.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf.
  wp_loadField.
  wp_apply (wp_sliding__clearMutable with "His_memLog").
  iIntros "His_memLog".

  wp_pures. iApply ("HΦ" $! (set memLog (λ _,
    (set slidingM.mutable (λ _ : u64, slidingM.endPos σ.(memLog))
    σ.(memLog))) σ
  )).
  iNamed "HmemLog_linv".
  iNamed "Hlinv_pers".
  iDestruct "HmemStart_txn" as "#HmemStart_txn".
  iDestruct "HmemEnd_txn" as "#HmemEnd_txn".
  iMod (txn_pos_valid_locked with "Hwal HmemEnd_txn Howntxns") as "(%HmemEnd_is_txn & Howntxns)".

  iAssert (txn_pos γ nextDiskEnd_txn_id σ.(memLog).(slidingM.mutable)) as "#HnextDiskEnd_txn0".
  { iNamed "HnextDiskEnd". iFrame "#". }
  iMod (txn_pos_valid_locked with "Hwal HnextDiskEnd_txn0 Howntxns") as "(%HnextDiskEnd_is_txn0 & Howntxns)".

  iDestruct "Hwal" as "[Hinv Hcirc]".
  iInv "Hinv" as (σs) "[Hinner Hp]" "Hclose".
  iDestruct "Hinner" as "(>%Hwf & Hmem & >Htxns_ctx & >γtxns & >HnextDiskEnd_inv & >Hdisk)".
  iDestruct (ghost_var_agree with "Howntxns γtxns") as %->.
  iMod (stable_alloc_end with "[$HnextDiskEnd $HnextDiskEnd_inv $Htxns_ctx $HmemEnd_txn]") as "H".
  iDestruct "H" as "(HnextDiskEnd & HnextDiskEnd_inv & Htxns_ctx & #Hstable)".
  iMod ("Hclose" with "[γtxns Hmem HnextDiskEnd_inv Hdisk Htxns_ctx Hp]").
  { iModIntro.
    iExists _. iFrame. done. }

  iModIntro.
  iDestruct (is_sliding_wf with "His_memLog") as %Hsliding_wf'.
  simpl.
  iSplitL; last by trivial.
  iFrame "HdiskEnd_circ Hstart_circ HownDiskEndMem_linv HownDiskEndMemTxn_linv HownInstalledPosMem_linv".
  iSplitR "Howntxns HownLoggerPos_linv HownLoggerTxn_linv HnextDiskEnd HownInstallerPosMem_linv HownInstallerTxnMem_linv HownInstalledTxnMem_linv".
  { iExists _; iFrame.
    iPureIntro.
    split_and!; simpl; auto; try word.
    rewrite /slidingM.endPos.
    unfold locked_wf, slidingM.wf in Hlocked_wf.
    word.
  }
  eapply is_txn_bound in HdiskEnd_txn as HdiskEnd_txn_bound.
  eapply is_txn_bound in HnextDiskEnd_is_txn0 as HnextDiskEnd_txn0_bound.
  destruct (decide (uint.Z σ.(memLog).(slidingM.mutable) ≤ uint.Z (slidingM.endPos σ.(memLog)))).
  2: {
    epose proof (wal_wf_txns_mono_pos Hwf HmemEnd_is_txn HnextDiskEnd_is_txn0). lia.
  }

  iExists installed_txn_id_mem, (length σs.(log_state.txns) - 1)%nat, σs.(log_state.txns), _, _, _, _; simpl.
  iFrame "Howntxns HownLoggerPos_linv HownLoggerTxn_linv".
  iFrame "HmemStart_txn HmemEnd_txn".
  iFrame "HownInstallerPosMem_linv HownInstallerTxnMem_linv HownInstalledTxnMem_linv".
  iFrame "% HinstalledTxn_lb".
  iSplit.
  2: {
    iNamed "HnextDiskEnd". iFrame "∗#%".
  }
  iSplit.
  { iPureIntro. cbn. lia. }
  iSplit.
  { iPureIntro. lia. }
  iNamed "HnextDiskEnd".
  iFrame "∗#".
  iSplit.
  2: {
    iPureIntro.
    rewrite /slidingM.endPos.
    word.
  }
  iPureIntro.
  rewrite /memLog_linv_txns !logIndex_set_mutable /slidingM.endPos
    /mwrb.logend /slidingM.logIndex /=.
  rewrite /memLog_linv_txns /mwrb.logend /slidingM.logIndex in Htxns.
  replace (S (_ - 1))%nat with (length σs.(log_state.txns)); last by lia.
  eapply (is_memLog_boundaries_move _ _ _ mwrb_us) in Htxns;
    last by reflexivity.
  simpl in Htxns.
  replace (uint.nat (word.add _ _) - uint.nat _)%nat
    with (length σ.(memLog).(slidingM.log)) by word.
  assumption.
Qed.

Theorem wp_endGroupTxn st γ :
  {{{ wal_linv st γ }}}
    WalogState__endGroupTxn #st
  {{{ RET #(); wal_linv st γ }}}.
Proof.
  iIntros (Φ) "Hlkinv HΦ".
  iNamed "Hlkinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  iNamed "His_memLog".
  iNamed "Hinv".
  iNamed "needFlush".
  wp_rec. wp_pures.
  wp_loadField.
  wp_storeField.

  iApply "HΦ".
  by iFrame "∗#".
Qed.

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
  erewrite HafterNextDiskEnd in H4; simplify_eq/=; eauto.
  { lia. }
  eapply is_txn_mid; [ done | apply H1 | apply H2 |].
  apply subslice_lookup_bound' in H3.
  lia.
Qed.

Lemma subslice_stable_nils2 γ σ (txn_id txn_id' : nat) pos :
  wal_wf σ ->
  is_txn σ.(log_state.txns) txn_id pos ->
  is_txn σ.(log_state.txns) txn_id' pos ->
  ( nextDiskEnd_inv γ σ.(log_state.txns) ∗
    txn_id [[γ.(stable_txn_ids_name)]]↦ro () ) -∗
  ⌜Forall (λ x, snd x = nil) (subslice (S txn_id) (S txn_id') σ.(log_state.txns))⌝.
Proof.
  intros.
  iIntros "[Hinv Hstable]".
  destruct (decide (txn_id ≤ txn_id')).
  { iApply subslice_stable_nils; eauto. }

  iPureIntro.
  rewrite /subslice.
  rewrite drop_ge; eauto.
  etransitivity; first by apply firstn_le_length.
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
  erewrite H3 in H5; simplify_eq/=; eauto.
  { lia. }
  eapply is_txn_mid; [ done | apply H1 | apply H2 | ].
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
    iSplitR; first done.
    iFrame "Htxns_ctx".
    iSplitL "Hstablectx Hstablero".
    { by iFrame. }
    iExists nextDiskEnd_txn_id.
    iSplitL "HownStableSet".
    { by iFrame "∗#". }
    rewrite subslice_zero_length.
    eapply is_txn_bound in HnextDiskEnd_txn.
    iPureIntro. intuition eauto; lia.
  }

  iCombine "HownStableSet Hstablectx" as "Hctx".
  iMod (map_alloc_ro with "Hctx") as "[Hctx #Hstable']"; eauto.
  iDestruct (big_sepM_insert with "[$Hstablero Hstable']") as "Hstablero"; eauto.
  iSplitR; first done.

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
  { iFrame "Hstable'". iFrame "Htxn_id'_pos".
    iPureIntro. intros. rewrite lookup_insert_ne; last by lia.
    eapply HnextDiskEnd_max_stable. lia. }
  eapply is_txn_bound in Histxn' as Histxn'_bound.
  iPureIntro. intuition try lia.
  eapply stable_sound_nils; eauto.
Qed.

End goose_lang.
