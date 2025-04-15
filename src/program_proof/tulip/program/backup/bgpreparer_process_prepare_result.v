From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_try_resign bgpreparer_in
  bgpreparer_accept bgpreparer_quorum_validated bgpreparer_quorum_accepted.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processPrepareResult
    (gpp : loc) (rid : u64) (res : rpres) rk ts cid gid γ :
    (1 < rk)%nat ->
    rid ∈ rids_all ->
    accept_outcome γ gid rid ts rk true res -∗
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processPrepareResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Hrk Hrid) "#Hacp".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processPrepareResult(rid uint64, res uint64) { @*)
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

    (*@     if !gpp.in(BGPP_PREPARING) {                                        @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__in _ BGPPPreparing with "Hgpp").
    iIntros "Hgpp".
    wp_pures.
    destruct (bool_decide (phase = BGPPPreparing)) eqn:Hpreparing; wp_pures; last first.
    { iApply "HΦ". by iFrame. }
    rewrite bool_decide_eq_true in Hpreparing. subst phase.

    (*@     // Prove that at this point the only possible phase is preparing.   @*)
    (*@     // Resource: Proposal map at rank 1 is true                         @*)
    (*@     // Invariant: UNPREPARING => proposal map at rank 1 is false: contradiction @*)
    (*@     // Invariant: Proposal entry present -> not VALIDATING or INQUIRING @*)
    (*@                                                                         @*)
    (*@     // Record success of preparing the replica.                         @*)
    (*@     gpp.accept(rid)                                                     @*)
    (*@                                                                         @*)
    (* Prove the only possible res here is [ReplicaOK]. *)
    destruct res; try done. simpl.
    iNamed "Hgpp". simpl.
    wp_apply (wp_BackupGroupPreparer__accept with "[Hacp] Hsrespm").
    { apply Hrid. }
    { done. }
    iIntros "Hsrespm".

    (*@     // A necessary condition to move to the PREPARED phase: validated on some @*)
    (*@     // classic quorum. TODO: We should be able to remove this check with the @*)
    (*@     // safe-propose invariant.                                          @*)
    (*@     if !gpp.quorumValidated() {                                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__quorumValidated with "[$Hvdm $Hnrps]").
    iIntros (vd) "(Hvdm & Hnrps & #Hqv)".
    wp_pures.
    destruct vd; wp_pures; last first.
    { iApply "HΦ". by iFrame "∗ #". }

    (*@     // Move to the PREPARED phase if receiving a classic quorum of positive @*)
    (*@     // prepare responses.                                               @*)
    (*@     if gpp.quorumAccepted() {                                           @*)
    (*@         gpp.phase = BGPP_PREPARED                                       @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupGroupPreparer__quorumAccepted with "[$Hsrespm $Hnrps]").
    { apply Hrk. }
    iIntros (ap) "(Hsrespm & Hnrps & #Hqp)".
    destruct ap; wp_pures.
    { iNamed "Hphase".
      wp_storeField.
      iApply "HΦ".
      iDestruct (own_backup_gpreparer_srespm_non_accepting_phase _ _ BGPPPrepared
                  with "Hsrespm") as "Hsrespm".
      { intros []. }
      by iFrame "∗ #".
    }
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
