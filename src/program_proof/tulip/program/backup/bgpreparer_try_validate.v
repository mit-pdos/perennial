From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_set_pwrs bgpreparer_validate.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__tryValidate
    (gpp : loc) (rid : u64) (vd : bool) (pwrsP : loc) (pwrs : dbmap) ts gid γ :
    rid ∈ rids_all ->
    (if vd then own_map pwrsP DfracDiscarded pwrs else True) -∗
    (if vd then safe_txn_pwrs γ gid ts pwrs else True) -∗
    (if vd then is_replica_validated_ts γ gid rid ts else True) -∗
    {{{ own_backup_gpreparer_pwrs gpp ts gid γ ∗ own_backup_gpreparer_vdm gpp ts gid γ }}}
      BackupGroupPreparer__tryValidate #gpp #rid #vd #pwrsP
    {{{ RET #();
        own_backup_gpreparer_pwrs gpp ts gid γ ∗ own_backup_gpreparer_vdm gpp ts gid γ
    }}}.
  Proof.
    iIntros (Hrid) "#Hm #Hsafepwrs #Hvd".
    iIntros (Φ) "!> [Hpwrs Hvdm] HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) tryValidate(rid uint64, vd bool, pwrs tulip.KVMap) { @*)
    (*@     if vd {                                                             @*)
    (*@         gpp.setPwrs(pwrs)                                               @*)
    (*@         gpp.validate(rid)                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_pures.
    destruct vd; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__setPwrs with "Hm Hsafepwrs Hpwrs").
      iIntros "Hpwrs".
      wp_apply (wp_BackupGroupPreparer__validate with "Hvd Hvdm").
      { apply Hrid. }
      iIntros "Hvdm".
      wp_pures.
      iApply "HΦ".
      by iFrame.
    }
    iApply "HΦ".
    by iFrame.
  Qed.

End program.
