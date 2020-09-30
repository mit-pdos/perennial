From RecordUpdate Require Import RecordSet.
From iris.algebra Require Import auth.

From Perennial.program_proof Require Import disk_lib.
From Perennial.program_proof Require Import wal.invariant.

Remove Hints fractional.into_sep_fractional : typeclass_instances.

Section goose_lang.
Context `{!heapG Σ}.
Context `{!walG Σ}.

Implicit Types (v:val) (z:Z).
Implicit Types (γ: wal_names).
Implicit Types (s: log_state.t) (memLog: slidingM.t) (txns: list (u64 * list update.t)).
Implicit Types (pos: u64) (txn_id: nat).

Context (P: log_state.t -> iProp Σ).
Let N := walN.
Let innerN := walN .@ "wal".
Let circN := walN .@ "circ".

Theorem wp_Walog__waitForSpace l γ σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked #σₛ.(memLock) ∗
      "#His_lock" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ)
  }}}
    Walog__waitForSpace #l
  {{{ σ, RET #();
      "Hlocked" ∷ locked #σₛ.(memLock)  ∗
      "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
      "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
      "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
      "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
      "%Hhas_space" ∷ ⌜length σ.(memLog).(slidingM.log) ≤ LogSz⌝
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iNamed "Hpre".
  wp_call.
  iNamed "Hlkinv".
  wp_apply (wp_forBreak_cond
              (λ b, "Hlocked" ∷ locked #σₛ.(memLock) ∗
                    "*" ∷ ∃ σ, "Hfields" ∷ wal_linv_fields σₛ.(wal_st) σ ∗
                               "HmemLog_linv" ∷ memLog_linv γ σ.(memLog) σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
                               "HdiskEnd_circ" ∷ diskEnd_linv γ σ.(diskEnd) σ.(locked_diskEnd_txn_id) ∗
                               "Hstart_circ" ∷ diskStart_linv γ σ.(memLog).(slidingM.start) ∗
                               "%Hbreak" ∷ ⌜b = false → (length σ.(memLog).(slidingM.log) ≤ LogSz)⌝
              )%I
              with "[] [-HΦ]").
  2: {
    iFrame.
    iExists _; iFrame "# ∗".
    iPureIntro. inversion 1.
  }
  { iIntros "!>" (Φ') "HI HΦ".
    iNamed "HI".
    iNamed "Hfields".
    iNamed "Hfield_ptsto".
    wp_loadField. wp_loadField.
    wp_apply (wp_log_len with "His_memLog"); iIntros "His_memLog".
    wp_pures.
    change (int.val (word.divu (word.sub 4096 8) 8)) with LogSz.
    wp_if_destruct.
    - wp_loadField.
      wp_apply (wp_condWait with "[-HΦ]"); [ iFrame "His_cond2 His_lock Hlocked" | ].
      { iExists _; iFrame "∗ #". iExists _; iFrame "% # ∗". }
      iIntros "(Hlocked&Hlkinv)".
      wp_pures.
      iApply "HΦ"; iFrame.
      iNamed "Hlkinv".
      iExists _; iFrame "# ∗".
      iPureIntro; inversion 1.
    - iApply "HΦ"; iFrame.
      iExists _; iFrame "∗ #".
      iSplit.
      { iExists _; by iFrame "# ∗". }
      iPureIntro.
      intros _.
      unfold locked_wf, slidingM.wf in Hlocked_wf.
      revert Heqb; word.
  }
  iIntros "HI"; iNamed "HI".
  specialize (Hbreak ltac:(auto)).
  iApply "HΦ".
  iFrameNamed. auto.
Qed.

Hint Unfold slidingM.logIndex slidingM.wf : word.

Lemma take_more {A} (n m: nat) (l: list A) :
  (n ≤ length l)%nat →
  take (n + m) l = take n l ++ take m (drop n l).
Proof.
  intros Hbound.
  rewrite -{1}(take_drop n l).
  rewrite -> take_app_ge by len.
  f_equal.
  f_equal.
  len.
Qed.

Lemma subslice_def {A} (n m: nat) (l: list A) :
  subslice n m l = drop n (take m l).
Proof. reflexivity. Qed.

Lemma subslice_comm {A} (n m: nat) (l: list A) :
  subslice n m l = take (m - n)%nat (drop n l).
Proof. rewrite /subslice skipn_firstn_comm //. Qed.

(** this is a way to re-fold subslice after commuting it, a useful inverse to
[subslice_comm] *)
Lemma subslice_take_drop {A} (n k: nat) (l: list A) :
  take k (drop n l) = subslice n (n + k) l.
Proof. rewrite /subslice firstn_skipn_comm //. Qed.

Theorem subslice_split_r {A} n m m' (l: list A) :
  (n ≤ m ≤ m')%nat →
  (m ≤ length l)%nat →
  subslice n m' l = subslice n m l ++ subslice m m' l.
Proof.
  intros Hbound1 Hbound2.
  rewrite /subslice.
  replace m' with (m + (m' - m))%nat by lia.
  rewrite -> take_more by lia.
  rewrite -> drop_app_le by len.
  f_equal.
  rewrite -> drop_app_le by len.
  rewrite -> (drop_ge (take m l)) by len.
  auto.
Qed.

Lemma circ_matches_extend cs txns installed_txn_id diskEnd_txn_id new_txn nextDiskEnd_txn_id :
  (installed_txn_id ≤ diskEnd_txn_id ≤ nextDiskEnd_txn_id)%nat →
  (nextDiskEnd_txn_id < length txns)%nat →
  has_updates new_txn (subslice (S diskEnd_txn_id) (S nextDiskEnd_txn_id) txns) →
  circ_matches_txns cs txns installed_txn_id diskEnd_txn_id →
  circ_matches_txns (set upds (λ u, u ++ new_txn) cs) txns installed_txn_id nextDiskEnd_txn_id.
Proof.
  rewrite /circ_matches_txns /=.
  intros ? ? ? [? ?].
  split; [ | lia ].
  rewrite -> (subslice_split_r installed_txn_id (S diskEnd_txn_id) (S nextDiskEnd_txn_id)) by lia.
  apply has_updates_app; auto.
Qed.

Lemma is_installed_extend_durable γ d txns installed_txn_id diskEnd_txn_id diskEnd_txn_id' :
  (diskEnd_txn_id ≤ diskEnd_txn_id' < length txns)%nat →
  is_installed γ d txns installed_txn_id diskEnd_txn_id -∗
  is_installed γ d txns installed_txn_id diskEnd_txn_id'.
Proof.
  intros Hbound.
  iNamed 1.
  iExists _, _; iFrame.
  iPureIntro; lia.
Qed.

Lemma circ_diskEnd_app σ upds' :
  circΣ.diskEnd (set circΣ.upds (λ u, u ++ upds') σ) =
  circΣ.diskEnd σ + length upds'.
Proof.
  rewrite /circΣ.diskEnd /=.
  len.
Qed.

Lemma logIndex_diff memLog pos1 pos2 :
  int.val memLog.(slidingM.start) ≤ int.val pos1 →
  (slidingM.logIndex memLog pos2 - slidingM.logIndex memLog pos1)%nat =
  (int.nat pos2 - int.nat pos1)%nat.
Proof.
  rewrite /slidingM.logIndex; intros.
  lia.
Qed.

Lemma subslice_lookup A (n m i : nat) (l : list A) :
  (n + i < m)%nat ->
  subslice n m l !! i = l !! (n + i)%nat.
Proof.
  intros.
  unfold subslice.
  rewrite lookup_drop.
  rewrite lookup_take; auto.
Qed.

Lemma subslice_lookup_bound A (n m i : nat) (l : list A) :
  is_Some (subslice n m l !! i) ->
  (n + i < m)%nat.
Proof.
  unfold subslice.
  intros.
  apply lookup_lt_is_Some_1 in H.
  rewrite drop_length in H.
  pose proof (firstn_le_length m l).
  lia.
Qed.

Lemma subslice_lookup_bound' A (n m i : nat) (l : list A) a :
  subslice n m l !! i = Some a ->
  (n + i < m)%nat.
Proof.
  intros.
  eapply subslice_lookup_bound; eauto.
Qed.

Lemma subslice_lookup_some A (n m i : nat) (l : list A) (a : A) :
  subslice n m l !! i = Some a ->
  l !! (n + i)%nat = Some a.
Proof.
  intros.
  pose proof H as H'.
  rewrite subslice_lookup in H'; eauto.
  eapply subslice_lookup_bound. eauto.
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

Lemma nextDiskEnd_nils γ σs (nextDiskEnd_txn_id nextDiskEnd_txn_id' : nat) m :
  wal_wf σs ->
  nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id' ->
  is_txn σs.(log_state.txns) nextDiskEnd_txn_id m ->
  is_txn σs.(log_state.txns) nextDiskEnd_txn_id' m ->
  ( nextDiskEnd_inv γ σs.(log_state.txns) ∗
    nextDiskEnd_txn_id [[γ.(stable_txn_ids_name)]]↦ro () ) -∗
  ⌜Forall (λ x, snd x = nil)
    (subslice (S nextDiskEnd_txn_id) (S nextDiskEnd_txn_id') σs.(log_state.txns))⌝.
Proof.
  intros.
  iIntros "[Hinv Hstable]".
  iNamed "Hinv".
  iDestruct (map_ro_valid with "Hstablectx Hstable") as "%Hvalid".
  iPureIntro.
  apply Forall_lookup_2; intros.
  apply subslice_lookup_some in H3 as H3'.
  assert (snd <$> σs.(log_state.txns) !! (S nextDiskEnd_txn_id + i)%nat = Some x.2).
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

Theorem wp_Walog__logAppend l circ_l γ σₛ :
  {{{ "#HmemLock" ∷ readonly (l ↦[Walog.S :: "memLock"] #σₛ.(memLock)) ∗
      "#HcondLogger" ∷ readonly (l ↦[Walog.S :: "condLogger"] #σₛ.(condLogger)) ∗
      "#HcondInstall" ∷ readonly (l ↦[Walog.S :: "condInstall"] #σₛ.(condInstall)) ∗
      "#d" ∷ readonly (l ↦[Walog.S :: "d"] σₛ.(wal_d)) ∗
      "#circ" ∷ readonly (l ↦[Walog.S :: "circ"] #σₛ.(circ)) ∗
      "#His_cond1" ∷ is_cond σₛ.(condLogger) #σₛ.(memLock) ∗
      "#His_cond2" ∷ is_cond σₛ.(condInstall) #σₛ.(memLock) ∗
      "#?" ∷ readonly (l ↦[Walog.S :: "st"] #σₛ.(wal_st)) ∗
      "#His_lock" ∷ is_lock N #σₛ.(memLock) (wal_linv σₛ.(wal_st) γ) ∗
      "#Hwal" ∷ is_wal P l γ ∗
      "Hlkinv" ∷ wal_linv σₛ.(wal_st) γ ∗
      "Hlocked" ∷ locked #σₛ.(memLock) ∗
      "Hlogger" ∷ logger_inv γ circ_l
  }}}
    Walog__logAppend #l #circ_l
  {{{ (progress:bool), RET #progress;
      wal_linv σₛ.(wal_st) γ ∗
      locked #σₛ.(memLock) ∗
      logger_inv γ circ_l
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iNamed "Hlogger".
  wp_call.
  wp_apply (wp_Walog__waitForSpace with "[$Hlkinv $Hlocked]").
  { iFrameNamed. iFrame "#". }
  iIntros (σ) "Hpost"; iNamed "Hpost".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".
  wp_loadField. wp_loadField.
  wp_loadField. wp_loadField.
  wp_apply (wp_sliding__takeFrom with "His_memLog").
  { word. }
  iIntros (q s) "(His_memLog&Hbufs)".
  wp_pures.
  wp_apply wp_slice_len; wp_pures.
  wp_if_destruct; wp_pures.
  { iApply "HΦ".
    iFrame "Hlocked".
    iSplitR "HnotLogging Hown_diskEnd_txn_id Happender HownLoggerPos_logger".
    - iExists _; iFrame.
      iExists _; iFrame "% ∗".
    - iFrame.
      iExists _; iFrame.
  }
  iNamed "HdiskEnd_circ".
  iMod (thread_own_get with "HdiskEnd_exactly HnotLogging") as
      "(HdiskEnd_exactly&Hlog_owned&HareLogging)";
    iNamed "Hlog_owned".
  iNamed "HmemLog_linv".
  iNamed "Hstart_circ".
  iDestruct "HmemStart_txn" as "#HmemStart_txn".
  iDestruct "HnextDiskEnd_txn" as "#HnextDiskEnd_txn".
  iMod (txn_pos_valid_locked with "Hwal HmemStart_txn Howntxns") as "(%HmemStart_txn&Howntxns)".
  iMod (txn_pos_valid_locked with "Hwal HnextDiskEnd_txn Howntxns") as "(%HnextDiskEnd_txn&Howntxns)".
  iMod (get_txns_are _ _ _ _ memStart_txn_id (S nextDiskEnd_txn_id) with "Howntxns Hwal") as "[Htxns_are Howntxns]"; eauto.
  { pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
    lia. }

  (* snapshot the position we're about to write to circular log *)
  iNamed "HownLoggerPos_logger".
  iMod (ghost_var_update_halves σ.(memLog).(slidingM.mutable) with "HownLoggerPos_logger HownLoggerPos_linv") as
        "[HownLoggerPos_logger HownLoggerPos_linv]".

  (* use this to also strip a later, which the [wp_loadField] tactic does not do *)
  wp_apply (wp_loadField_ro with "HmemLock"); first by auto.
  iDestruct "Htxns_are" as "#Htxns_are".
  wp_apply (release_spec with "[-HΦ HareLogging HdiskEnd_is Happender Hbufs Hown_diskEnd_txn_id γdiskEnd_txn_id1 $His_lock $Hlocked HownLoggerPos_logger]").
  { iExists _; iFrame "# ∗".
    iSplitR "Howntxns HmemEnd_txn HownStableSet HownLoggerPos_linv".
    - iExists _; iFrame "% ∗".
    - iExists _, _, _, _, _.
      iFrame "HownLoggerPos_linv".
      iFrame "# % ∗".
      iPureIntro. unfold locked_wf in *. intuition lia.
  }
  wp_loadField.
  iDestruct "Hwal" as "[Hwal Hcirc]".
  wp_apply (wp_circular__Append _ _
                              (∃ (nextDiskEnd_txn_id' : nat),
                               "γdiskEnd_txn_id1" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/4) nextDiskEnd_txn_id' ∗
                               "Hown_diskEnd_txn_id" ∷ ghost_var γ.(diskEnd_txn_id_name) (1/2) nextDiskEnd_txn_id' ∗
                               "#HnextDiskEnd_txn_pos" ∷ txn_pos γ nextDiskEnd_txn_id' σ.(memLog).(slidingM.mutable) ∗
                               "%HnextDiskEnd_txn_id'" ∷ ⌜nextDiskEnd_txn_id ≤ nextDiskEnd_txn_id'⌝)
              with "[$Hbufs $HdiskEnd_is $Happender $Hcirc $Hstart_at_least Hown_diskEnd_txn_id γdiskEnd_txn_id1]").
  { rewrite subslice_length; word. }
  { rewrite subslice_length; word. }

  { (* Append fupd *)
    rewrite /circular_pred.
    iIntros (cs) "(%Hcirc_wf&%HdiskEnd_eq&Hcirc_ctx)".
    iIntros (cs' [] [Htrans Hcirc_wf']).
    simpl in Htrans; monad_inv.
    iInv "Hwal" as (σs) "[Hinner HP]".

    iDestruct "Hinner" as "(>%Hwf&Hmem&>?&>?&>?&>?)"; iNamed.
    iNamed "Hdisk".
    iDestruct (ghost_var_agree with "Hcirc_ctx Howncs") as %Heq; subst cs0.
    iDestruct (txns_are_sound with "Htxns_ctx Htxns_are") as %Htxns_are.
    iDestruct (txn_pos_valid_general with "Htxns_ctx HmemStart_txn") as %HmemStart'.
    iDestruct (txn_pos_valid_general with "Htxns_ctx HnextDiskEnd_txn") as %HnextDiskEnd'.
    iMod (ghost_var_update_halves with "Hcirc_ctx Howncs") as "[$ Howncs]".
    iNamed "Hdisk".
    iDestruct (ghost_var_agree with "γdiskEnd_txn_id1 γdiskEnd_txn_id2") as %?; subst.
    iCombine "γdiskEnd_txn_id1 γdiskEnd_txn_id2" as "γdiskEnd_txn_id".
    (* If we used "1/2/2" instead of "1/4" (and fixed some Perennial-induced typeclass oddities),
       we could avoid this. *)
    assert (1/4 + 1/4 = 1/2)%Qp as ->.
    { apply (bool_decide_unpack _); by compute. }
    iDestruct (ghost_var_agree with "γdiskEnd_txn_id Hown_diskEnd_txn_id") as %?; subst.

    edestruct (is_txn_round_up σs.(log_state.txns) nextDiskEnd_txn_id) as [nextDiskEnd_txn_id' Hhighest]; first by eauto.
    iDestruct (txns_ctx_txn_pos _ _ nextDiskEnd_txn_id' with "Htxns_ctx") as "#HnextDiskEnd_txn_pos".
    { eapply is_highest_weaken; eauto. }

    iMod (ghost_var_update_halves nextDiskEnd_txn_id' with "γdiskEnd_txn_id Hown_diskEnd_txn_id") as
        "[γdiskEnd_txn_id Hown_diskEnd_txn_id]".
    (* FIXME: due to Perennial removing some TC hints, this pattern cannot be inlined into the above. *)
    iDestruct "γdiskEnd_txn_id" as "[γdiskEnd_txn_id out_txn_id]".
    assert (1/2/2 = 1/4)%Qp as ->.
    { apply (bool_decide_unpack _); by compute. }
    eapply Hhighest in HnextDiskEnd' as HnextDiskEnd_nextDiskEnd'.
    eapply is_highest_weaken in Hhighest as HnextDiskEnd'_txn.
    iSplitR "Hown_diskEnd_txn_id out_txn_id".
    2: {
      iExists _. iFrame. iFrame "HnextDiskEnd_txn_pos".
      iPureIntro. lia.
    }

    iDestruct (nextDiskEnd_nils with "[$HnextDiskEnd_inv $HnextDiskEnd_stable]") as "%Hnils".
    { eassumption. }
    2: { eassumption. }
    2: { eapply HnextDiskEnd'_txn. }
    { lia. }

    iModIntro.
    iNext.
    iExists _; iFrame.
    iSplitR; auto.
    iExists _; iFrame.
    iNamed "circ.end".
    iExists installed_txn_id, nextDiskEnd_txn_id'.
    iFrame "# ∗".
    iSplitL "Hinstalled".
    { iApply (is_installed_extend_durable with "Hinstalled").
      apply is_txn_bound in HnextDiskEnd'_txn.
      word. }
    iSplitL "Hdurable".
    { iDestruct "Hdurable" as %Hmatches.
      iPureIntro.
      eapply circ_matches_extend; eauto; try lia.
      { split; try lia.
        destruct Hmatches. done. }
      { apply is_txn_bound in HnextDiskEnd'_txn; auto. }
      pose proof (is_txn_bound _ _ _ HnextDiskEnd_txn).
      rewrite -> subslice_length in Htxns_are by lia.
      replace (memStart_txn_id + (S nextDiskEnd_txn_id - memStart_txn_id))%nat
              with (S nextDiskEnd_txn_id) in Htxns_are by lia.
      apply (subslice_suffix_eq _ _ _ (S σ.(locked_diskEnd_txn_id))) in Htxns_are; last by lia.
      rewrite -Htxns_are in His_nextDiskEnd.
      pose proof (is_txn_bound _ _ _ HnextDiskEnd').
      rewrite -> (subslice_split_r _ (S nextDiskEnd_txn_id) _ σs.(log_state.txns)) by lia.
      eapply has_updates_app_nils; eauto.
    }
    rewrite /is_durable_txn.
    iExists σ.(memLog).(slidingM.mutable).
    iSplit.
    { iPureIntro.
      lia. }
    iSplit.
    { iPureIntro.
      simpl.
      rewrite circ_diskEnd_app.
      rewrite -> subslice_length by word.
      rewrite -> logIndex_diff by word.
      word. }
    { iPureIntro. done. }
  }
  rewrite -> subslice_length by word.
  iIntros "(Hpost&Hupds&Hcirc_appender&HdiskEnd_is)"; iNamed "Hpost".
  wp_loadField.
  wp_apply (acquire_spec with "His_lock").
  iIntros "(His_locked&Hlockinv)".
  iNamed "Hlockinv".
  iNamed "Hfields".
  iNamed "Hfield_ptsto".

  (* Open up memlog lock invariant to prove we still have the same logger pos *)
  iRename "HmemStart_txn" into "HmemStart_txn_old".
  iRename "HnextDiskEnd_txn" into "HnextDiskEnd_txn_old".
  iRename "HnextDiskEnd_stable" into "HnextDiskEnd_stable_old".
  iRename "HmemEnd_txn" into "HmemEnd_txn_old".
  iNamed "HmemLog_linv".
  iDestruct (ghost_var_agree with "HownLoggerPos_logger HownLoggerPos_linv") as %Heqloggerpos; subst.

  iRename "HdiskEnd_at_least" into "HdiskEnd_at_least_old".
  iDestruct (diskEnd_is_to_at_least with "HdiskEnd_is") as "#HdiskEnd_at_least_new".
  iNamed "HdiskEnd_circ".
  iMod (thread_own_put with "HdiskEnd_exactly HareLogging [HdiskEnd_is γdiskEnd_txn_id1]")
    as "[HdiskEnd_exactly HnotLogging]"; first by iAccu.
  wp_apply wp_slice_len.
  wp_loadField. wp_storeField.
  wp_loadField.
  wp_apply (wp_condBroadcast with "His_cond1").
  wp_loadField.
  wp_apply (wp_condBroadcast with "His_cond2").
  wp_pures.
  iApply "HΦ".
  iFrame "His_locked".
  iSplitR "Hcirc_appender HnotLogging Hown_diskEnd_txn_id HownLoggerPos_logger".
  - iExists (set diskEnd (λ _, int.val σ.(diskEnd) + int.val s.(Slice.sz))
            (set locked_diskEnd_txn_id (λ _, nextDiskEnd_txn_id') σ0)).
    iDestruct (updates_slice_frag_len with "Hupds") as "%Hupds_len".
    rewrite subslice_length in Hupds_len; last by word.
    rewrite logIndex_diff in Hupds_len; last by word.
    simpl.
    iFrame.
    iSplitL "HmemLog Hshutdown Hnthread His_memLog".
    { iExists _. iFrame.
      iPureIntro.
      rewrite Hupds_len.
      unfold locked_wf in *. simpl.
      intuition try lia.
      { word. }
      { word. }
    }
    iSplitR "Howntxns HownStableSet HownLoggerPos_linv".
    {
      repeat rewrite logIndex_diff; last by word.
      iSplitR "HdiskEnd_exactly".
      2: {
        rewrite Hupds_len.
        replace (int.val
            (int.val σ.(diskEnd) +
             (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat)) with
          (int.val σ.(diskEnd) +
                           (int.nat σ.(memLog).(slidingM.mutable) -
                            int.nat σ.(diskEnd))%nat).
        { iFrame. }
        word.
      }
      rewrite Hupds_len.
      replace (int.val
       (int.val σ.(diskEnd) +
        (int.nat σ.(memLog).(slidingM.mutable) - int.nat σ.(diskEnd))%nat))
        with (int.val σ.(diskEnd) +
                             (int.nat σ.(memLog).(slidingM.mutable) -
                              int.nat σ.(diskEnd))%nat) by word.
      iFrame "HdiskEnd_at_least_new".
    }

    iExists _, _, _, _, _.
    iFrame.
    iFrame "HmemStart_txn HmemEnd_txn".
    iFrame "HnextDiskEnd_txn HnextDiskEnd_stable".

    iPureIntro.
    intuition idtac.
    all: try word.
    + admit.
    + admit.
      (* We probably need to explicitly consider the case that our
         nextDiskEnd_txn_id' is higher than nextDiskEnd_txn_id0.
         In this case, while we are still in a WP proof, we should
         allocate a stability fact for nextDiskEnd_txn_id' (and prove
         a lemma that says higher txn IDs for the same pos as a stable
         txn ID are also stable). *)
    + rewrite Hupds_len.
      admit.
      (* Even trickier: actually we should have done another round
         of [is_txn_round_up] when we re-acquired the lock!  So, this
         means we should get a nextDiskEnd_txn_id'' that is highest
         as of the time we re-acquired the lock.. *)
    + admit.

  - iFrame.
    iSplitR "HownLoggerPos_logger".
    + iExists _; iFrame.
    + iExists _; iFrame.
Admitted.

Theorem wp_Walog__logger l circ_l γ :
  {{{ "#Hwal" ∷ is_wal P l γ ∗
      "Hlogger" ∷ logger_inv γ circ_l
  }}}
    Walog__logger #l #circ_l
  {{{ RET #(); True }}}.
Proof.
  iIntros (Φ) "Hpre HΦ"; iNamed "Hpre".
  iMod (is_wal_read_mem with "Hwal") as "#Hmem".
  wp_call.
  iNamed "Hmem".
  iNamed "Hstfields".
  wp_loadField.
  wp_apply (acquire_spec with "[$]").
  iIntros "(Hlk_held&Hlkinv)".
  wp_pures.

  wp_apply (wp_inc_nthread with "[$st $Hlkinv]"); iIntros "Hlkinv".
  wp_pures.
  wp_bind (For _ _ _).
  wp_apply (wp_forBreak_cond (fun b => wal_linv σₛ.(wal_st) γ ∗ locked #σₛ.(memLock) ∗ logger_inv γ circ_l)%I
              with "[] [$]").
  { iIntros "!>" (Φ') "(Hlkinv&Hlk_held&Hlogger) HΦ".
    wp_apply (wp_load_shutdown with "[$st $Hlkinv]"); iIntros (shutdown) "Hlkinv".
    wp_pures.
    wp_if_destruct.
    - wp_pures.
      wp_apply (wp_Walog__logAppend with "[$Hlkinv $Hlk_held $Hlogger]").
      { iFrame "# ∗". }
      iIntros (progress) "(Hlkinv&Hlk_held&Hlogger)".
      wp_pures.
      wp_if_destruct.
      + wp_loadField.
        wp_apply (wp_condWait with "[$cond_logger $lk $Hlkinv $Hlk_held]").
        iIntros "(Hlk_held&Hlkinv)".
        wp_pures.
        iApply ("HΦ" with "[$]").
      + wp_pures. iApply ("HΦ" with "[$]").
    - iApply ("HΦ" with "[$]").
  }
  iIntros "(Hlkinv&Hlk_held&Hlogger)".
  wp_apply util_proof.wp_DPrintf.
  wp_apply (wp_dec_nthread with "[$st $Hlkinv]"); iIntros "Hlkinv".
  wp_loadField.
  wp_apply (wp_condSignal with "cond_shut").
  wp_loadField.
  wp_apply (release_spec with "[$lk $Hlk_held $Hlkinv]").
  iApply ("HΦ" with "[//]").
Qed.

End goose_lang.
