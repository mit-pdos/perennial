From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.invariance Require Import propose.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_try_resign bgpreparer_in
  bgpreparer_validate bgpreparer_quorum_validated bgpreparer_become_preparing.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__processValidateResult
    (gpp : loc) (rid : u64) (res : rpres) rk ts cid gid γ :
    (1 < rk)%nat ->
    rid ∈ rids_all ->
    gid ∈ gids_all ->
    validate_outcome γ gid rid ts res -∗
    know_tulip_inv γ -∗
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__processValidateResult #gpp #rid #(rpres_to_u64 res)
    {{{ RET #(); own_backup_gpreparer gpp rk ts cid gid γ }}}.
  Proof.
    iIntros (Hrk Hrid Hgid) "#Hvd #Hinv".
    iIntros (Φ) "!> Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) processValidateResult(rid uint64, res uint64) { @*)
    (*@     // Result is ready or another backup coordinator has become live.   @*)
    (*@     if gpp.tryResign(res) {                                             @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__tryResign with "[] Hgpp").
    { by destruct res. }
    iIntros (resigned phase') "(Hgpp & %Hres & %Hresigned)".
    clear phase. rename phase' into phase.
    destruct resigned; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     // Skip since the coordinator is already in the second phase.       @*)
    (*@     if !gpp.in(BGPP_VALIDATING) {                                       @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply (wp_BackupGroupPreparer__in _ BGPPValidating with "Hgpp").
    iIntros "Hgpp".
    wp_pures.
    destruct (bool_decide (phase = BGPPValidating)) eqn:Hvalidating; wp_pures; last first.
    { iApply "HΦ". by iFrame. }

    (*@     // Validation fails; nothing to record.                             @*)
    (*@     if res == tulip.REPLICA_FAILED_VALIDATION {                         @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set c := bool_decide _.
    destruct c eqn:Hfailed; wp_pures.
    { iApply "HΦ". by iFrame. }

    (*@     // Record success of validation.                                    @*)
    (*@     gpp.validate(rid)                                                   @*)
    (*@                                                                         @*)
    (* Prove the only possible res here is [ReplicaOK]. *)
    destruct res; try done. simpl.
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__validate with "Hvd Hvdm").
    { apply Hrid. }
    iIntros "Hvdm".
    
    (*@     // To be in the VALIDATING phase, we know the transaction must not have fast @*)
    (*@     // unprepared (need an invariant to remember this fact established when @*)
    (*@     // transiting from INQUIRING to VALIDATING in @ProcessInquireResult). @*)
    (*@                                                                         @*)
    (*@     // Move to PREPARING phase if it reaches a majority.                @*)
    (*@     if gpp.quorumValidated() {                                          @*)
    (*@         gpp.becomePreparing()                                           @*)
    (*@         return                                                          @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_BackupGroupPreparer__quorumValidated with "[$Hvdm $Hnrps]").
    iIntros (vd) "(Hvdm & Hnrps & #Hqv)".
    destruct vd; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__becomePreparing with "[$Hsrespm $Hphase]").
      iIntros "[Hsrespm Hphase]".
      wp_pures.
      rewrite bool_decide_eq_true in Hvalidating. subst phase.
      simpl.
      iDestruct "Hsafe" as "[Hsafepsl Hqvoted]".
      iApply "HΦ".
      iAssert (exclusive_proposal γ gid ts rk)%I with "[Htoken]" as "Hexcl".
      { rewrite /exclusive_proposal.
        destruct (decide (rk = 1)%nat); first lia.
        rewrite /safe_backup_token.
        iDestruct "Hqvoted" as (rids_votes) "[#Hvotes %Hvotecq]".
        by iFrame "∗ # %".
      }
      iAssert (|={⊤}=> is_group_prepare_proposal γ gid ts rk true)%I with "[Hexcl]" as "> #Hpsl".
      { iDestruct "Hinv" as (proph) "Hinv".
        iInv "Hinv" as "> HinvO" "HinvC".
        iNamed "HinvO".
        iDestruct (big_sepS_elem_of_acc with "Hgroups") as "[Hgroup HgroupsC]".
        { apply Hgid. }
        iMod (group_inv_propose with "Hsafepsl Hexcl Hgroup") as "[Hgroup #Hppsl]".
        { clear -Hrk. lia. }
        iDestruct ("HgroupsC" with "Hgroup") as "Hgroups".
        by iMod ("HinvC" with "[$Htxnsys $Hkeys $Hgroups $Hrgs]") as "_".
      }
      by iFrame "∗ #".
    }
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
