From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_try_resign bgpreparer_in
  bgpreparer_accept bgpreparer_quorum_accepted.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processUnprepareResult
    (gpp : loc) (rid : u64) (res : rpres) rk ts cid gid γ :
    (1 < rk)%nat ->
    rid ∈ rids_all ->
    accept_outcome γ gid rid ts rk false res -∗
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processUnprepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Hrk Hrid) "#Hacp".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processUnprepareResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or another backup coordinator has become live.   @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp".
    wp_pures.
    wp_apply (wp_BackupGroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned phase') "(Hgpp & %Hres & %Hresigned)".
    clear phase. rename phase' into phase.
    destruct resigned; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     if !gpp.in(BGPP_UNPREPARING) {                                      @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__in _ BGPPUnpreparing with "Hgpp").
    iIntros "Hgpp".
    wp_pures.
    destruct (bool_decide (phase = BGPPUnpreparing)) eqn:Hunpreparing; wp_pures; last first.
    { iApply "HΦ". by iFrame. }
    rewrite bool_decide_eq_true in Hunpreparing. subst phase.

    (*@     // Record success of unpreparing the replica.                       @*)
    (*@     gpp.accept(rid)                                                     @*)
    (*@                                                                         @*)
    (* Prove the only possible res here is [ReplicaOK]. *)
    destruct res; try done. simpl.
    iNamed "Hgpp". simpl.
    wp_apply (wp_BackupGroupPreparer__accept with "[Hacp] Hsrespm").
    { apply Hrid. }
    { done. }
    iIntros "Hsrespm".

    (*@     // Move to the ABORTED phase if obtaining a classic quorum of positive @*)
    (*@     // unprepare responses.                                             @*)
    (*@     if gpp.quorumAccepted() {                                           @*)
    (*@         gpp.phase = BGPP_ABORTED                                        @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupGroupPreparer__quorumAccepted with "[$Hsrespm $Hnrps]").
    { apply Hrk. }
    iIntros (ap) "(Hsrespm & Hnrps & #Hqp)".
    destruct ap; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPAborted
                  with "Hsrespm") as "Hsrespm".
      { intros []. }
      by iFrame "∗ #".
    }
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
