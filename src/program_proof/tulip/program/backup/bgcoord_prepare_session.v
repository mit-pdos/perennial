From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr bgcoord_send bgcoord_finalized
  bgcoord_next_prepare_action bgcoord_get_pwrs.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

 Theorem wp_BackupGroupCoordinator__PrepareSession
    (gcoord : loc) (rid : u64) (tsW : u64) (rkW : u64) (ptgsP : Slice.t)
    (ptgs : txnptgs) addrm gid γ :
    let ts := uint.nat tsW in
    let rk := uint.nat rkW in
    valid_ts ts ->
    rid ∈ dom addrm ->
    is_lnrz_tid γ ts -∗
    safe_txn_ptgs γ ts ptgs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__PrepareSession #gcoord #rid #tsW #rkW (to_val ptgsP)
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts rank Hvts Hrid) "#Hlnrz #Hsafeptgs #Hptgs #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *BackupGroupCoordinator) PrepareSession(rid, ts, rank uint64, ptgs []uint64) { @*)
    (*@     for !gcoord.Finalized() {                                           @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak_cond (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_BackupGroupCoordinator__Finalized with "[$Hgcoord]").
      iIntros (finalized) "_".
      destruct finalized eqn:Hfinalized; wp_pures.
      { by iApply "HΦ". }

      (*@         act := gcoord.NextPrepareAction(rid)                            @*)
      (*@                                                                         @*)
      wp_apply (wp_BackupGroupCoordinator__NextPrepareAction with "[$Hgcoord]").
      iIntros (act) "#Hsafea".
      wp_pures.

      (*@         if act == BGPP_INQUIRE {                                        @*)
      (*@             gcoord.SendInquire(rid, ts, rank)                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hinquire; wp_pures.
      { (* FIXME: ugly proof *)
        iPoseProof "Hgcoord" as "Hgcoord'".
        iNamed "Hgcoord'".
        wp_loadField.
        wp_apply (wp_BackupGroupCoordinator__SendInquire with "Hgcoord").
        { apply Hvts. }
        { apply Hrid. }
        wp_pures.
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         } else if act == BGPP_VALIDATE {                                @*)
      (*@             pwrs, ok := gcoord.GetPwrs()                                @*)
      (*@             // The write set should be available in the VALIDATING phase; it @*)
      (*@             // should not require the check.                            @*)
      (*@             if ok {                                                     @*)
      (*@                 gcoord.SendValidate(rid, ts, rank, pwrs, ptgs)          @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hvalidate; wp_pures.
      { wp_apply (wp_BackupGroupCoordinator__GetPwrs with "[$Hgcoord]").
        iIntros (pwrsP ok) "Hpwrs".
        wp_pures.
        destruct ok; wp_pures.
        { iDestruct "Hpwrs" as (pwrs) "[#Hpwrs #Hsafepwrs]".
          wp_apply (wp_BackupGroupCoordinator__SendValidate
                     with "Hlnrz Hsafepwrs Hsafeptgs Hptgs Hgcoord Hpwrs").
          { apply Hrid. }
          wp_pures.
          by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
        }
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         } else if act == BGPP_PREPARE {                                 @*)
      (*@             gcoord.SendPrepare(rid, ts, rank)                           @*)
      (*@                                                                         @*)
      case_bool_decide as Hprepare; wp_pures.
      { destruct act; try done. simpl.
        wp_apply (wp_BackupGroupCoordinator__SendPrepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_apply wp_Sleep.
        wp_pures.
        by iApply "HΦ".
      }

      (*@         } else if act == BGPP_UNPREPARE {                               @*)
      (*@             gcoord.SendUnprepare(rid, ts, rank)                         @*)
      (*@                                                                         @*)
      case_bool_decide as Hunprepare; wp_pures.
      { destruct act; try done. simpl.
        wp_apply (wp_BackupGroupCoordinator__SendUnprepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_apply wp_Sleep.
        wp_pures.
        by iApply "HΦ".
      }

      (*@         } else if act == BGPP_REFRESH {                                 @*)
      (*@             gcoord.SendRefresh(rid, ts, rank)                           @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      case_bool_decide as Hrefresh; wp_pures.
      { wp_apply (wp_BackupGroupCoordinator__SendRefresh with "Hgcoord").
        { apply Hrid. }
        wp_pures.
        by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
      }

      (*@         if act == BGPP_REFRESH {                                        @*)
      (*@             primitive.Sleep(params.NS_SEND_REFRESH)                     @*)
      (*@         } else {                                                        @*)
      (*@             // The optimal time to sleep is the time required to arrive at a @*)
      (*@             // prepare decision. Waking up too frequently means sending @*)
      (*@             // unnecessary messages, too infrequently means longer latency when @*)
      (*@             // messages are lost.                                       @*)
      (*@             //                                                          @*)
      (*@             // This might not be optimal for slow-path prepare. Consider @*)
      (*@             // optimize this with CV wait and timeout.                  @*)
      (*@             primitive.Sleep(params.NS_RESEND_PREPARE)                   @*)
      (*@         }                                                               @*)
      (*@     }                                                                   @*)
      (*@ }                                                                       @*)
      by case_bool_decide; wp_pures; wp_apply wp_Sleep; wp_pures; iApply "HΦ".
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
