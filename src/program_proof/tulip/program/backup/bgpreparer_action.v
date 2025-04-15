From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgpreparer_repr bgpreparer_get_phase bgpreparer_inquired
  bgpreparer_validated bgpreparer_accepted.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupPreparer__action (gpp : loc) (rid : u64) rk ts cid gid γ :
    {{{ own_backup_gpreparer gpp rk ts cid gid γ }}}
      BackupGroupPreparer__action #gpp #rid
    {{{ (action : bgppaction), RET #(bgppaction_to_u64 action); 
        own_backup_gpreparer gpp rk ts cid gid γ ∗
        safe_backup_gpreparer_action γ ts gid rk action
    }}}.
  Proof.
    iIntros (Φ) "Hgpp HΦ".
    wp_rec.

    (*@ func (gpp *BackupGroupPreparer) action(rid uint64) uint64 {             @*)
    (*@     phase := gpp.getPhase()                                             @*)
    (*@                                                                         @*)
    iNamed "Hgpp".
    wp_apply (wp_BackupGroupPreparer__getPhase with "Hgpp").
    iIntros "[Hgpp _]".
    wp_pures.
    iNamed "Hgpp".

    (*@     // Inquire the transaction status on replica @rid.                  @*)
    (*@     if phase == BGPP_INQUIRING {                                        @*)
    (*@         // Check if the inquire response (i.e., latest proposal + validation @*)
    (*@         // status) for replica @rid is available.                       @*)
    (*@         inquired := gpp.inquired(rid)                                   @*)
    (*@         if !inquired {                                                  @*)
    (*@             // Have not received the inquire response.                  @*)
    (*@             return BGPP_INQUIRE                                         @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hinquiring; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__inquired with "Hpps").
      iIntros (inquired) "Hpps".
      wp_pures.
      destruct inquired; wp_pures; last first.
      { iApply ("HΦ" $! BGPPInquire). by iFrame. }
      iApply ("HΦ" $! BGPPRefresh). by iFrame.
    }

    (*@     // Validate the transaction.                                        @*)
    (*@     if phase == BGPP_VALIDATING {                                       @*)
    (*@         // Check if the inquire response (i.e., latest proposal + validation @*)
    (*@         // status) for replica @rid is available.                       @*)
    (*@         inquired := gpp.inquired(rid)                                   @*)
    (*@         if !inquired {                                                  @*)
    (*@             // Have not received inquire response.                      @*)
    (*@             return BGPP_INQUIRE                                         @*)
    (*@         }                                                               @*)
    (*@         // The inquire response is available. Now check if the transaction has @*)
    (*@         // been validated on replica @rid.                              @*)
    (*@         validated := gpp.validated(rid)                                 @*)
    (*@         if !validated {                                                 @*)
    (*@             return BGPP_VALIDATE                                        @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hvalidating; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__inquired with "Hpps").
      iIntros (inquired) "Hpps".
      wp_pures.
      destruct inquired; wp_pures; last first.
      { iApply ("HΦ" $! BGPPInquire). by iFrame. }
      wp_apply (wp_BackupGroupPreparer__validated with "Hvdm").
      iIntros (validated) "Hvdm".
      wp_pures.
      destruct validated; wp_pures; last first.
      { iApply ("HΦ" $! BGPPValidate). by iFrame. }
      iApply ("HΦ" $! BGPPRefresh). by iFrame.
    }

    (*@     // Prepare the transaction.                                         @*)
    (*@     if phase == BGPP_PREPARING {                                        @*)
    (*@         prepared := gpp.accepted(rid)                                   @*)
    (*@         if !prepared {                                                  @*)
    (*@             return BGPP_PREPARE                                         @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hpreparing; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__accepted with "Hsrespm").
      iIntros (prepared) "Hsrespm".
      wp_pures.
      destruct prepared; wp_pures; last first.
      { iApply ("HΦ" $! BGPPPrepare).
        destruct phase; try done.
        by iFrame "∗ #".
      }
      iApply ("HΦ" $! BGPPRefresh). by iFrame.
    }

    (*@     // Unprepare the transaction.                                       @*)
    (*@     if phase == BGPP_UNPREPARING {                                      @*)
    (*@         unprepared := gpp.accepted(rid)                                 @*)
    (*@         if !unprepared {                                                @*)
    (*@             return BGPP_UNPREPARE                                       @*)
    (*@         }                                                               @*)
    (*@         return BGPP_REFRESH                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    case_bool_decide as Hunpreparing; wp_pures.
    { wp_apply (wp_BackupGroupPreparer__accepted with "Hsrespm").
      iIntros (unprepared) "Hsrespm".
      wp_pures.
      destruct unprepared; wp_pures; last first.
      { iApply ("HΦ" $! BGPPUnprepare).
        destruct phase; try done.
        by iFrame "∗ #".
      }
      iApply ("HΦ" $! BGPPRefresh). by iFrame.
    }

    (*@     return BGPP_REFRESH                                                 @*)
    (*@ }                                                                       @*)
    iApply ("HΦ" $! BGPPRefresh). by iFrame.
  Qed.

End program.
