From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr gcoord_send gcoord_next_prepare_action gpreparer_action.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__waitOnResendSignal (gcoord : loc) gid γ :
    is_gcoord gcoord gid γ -∗
    {{{ True }}}
      GroupCoordinator__waitOnResendSignal #gcoord
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hgcoord" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) waitOnResendSignal() {                  @*)
    (*@     gcoord.mu.Lock()                                                    @*)
    (*@     gcoord.cvrs.Wait()                                                  @*)
    (*@     gcoord.mu.Unlock()                                                  @*)
    (*@ }                                                                       @*)
    do 2 iNamed "Hgcoord".
    wp_loadField.
    wp_apply (wp_Mutex__Lock with "Hlock").
    iIntros "[Hlocked Hgcoord]".
    wp_loadField.
    wp_apply (wp_Cond__Wait with "[$Hlock $Hcvrs $Hlocked $Hgcoord]").
    iIntros "[Hlocked Hgcoord]".
    wp_loadField.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $Hgcoord]").
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_GroupCoordinator__PrepareSession
    (gcoord : loc) (rid : u64) (tsW : u64) (ptgsP : Slice.t) (pwrsP : loc)
    (pwrs : dbmap) (ptgs : txnptgs) addrm gid γ :
    let ts := uint.nat tsW in
    rid ∈ dom addrm ->
    is_lnrz_tid γ ts -∗
    safe_txn_pwrs γ gid ts pwrs -∗
    safe_txn_ptgs γ ts ptgs -∗
    own_map pwrsP DfracDiscarded pwrs -∗
    is_txnptgs_in_slice ptgsP ptgs -∗
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__PrepareSession #gcoord #rid #tsW (to_val ptgsP) #pwrsP
    {{{ RET #(); True }}}.
  Proof.
    iIntros (ts Hrid) "#Hlnrz #Hsafepwrs #Hsafeptgs #Hpwrs #Hptgs #Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec. wp_pures.

    (*@ func (gcoord *GroupCoordinator) PrepareSession(rid uint64, ts uint64, ptgs []uint64, pwrs map[string]tulip.Value) { @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I with "[] []"); last first; first 1 last.
    { done. }
    { clear Φ.

      (*@         act, attached := gcoord.NextPrepareAction(rid, ts)              @*)
      (*@                                                                         @*)
      iIntros (Φ) "!> _ HΦ".
      wp_apply (wp_GroupCoordinator__NextPrepareAction).
      { by iFrame "Hgcoord". }
      iIntros (action ok) "#Hsafea".
      wp_pures.

      (*@         if !attached {                                                  @*)
      (*@             break                                                       @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      destruct ok; wp_pures; last by iApply "HΦ".

      (*@         if act == GPP_FAST_PREPARE {                                    @*)
      (*@             gcoord.SendFastPrepare(rid, ts, pwrs, ptgs)                 @*)
      (*@         } else if act == GPP_VALIDATE {                                 @*)
      (*@             gcoord.SendValidate(rid, ts, pwrs, ptgs)                    @*)
      (*@         } else if act == GPP_PREPARE {                                  @*)
      (*@             gcoord.SendPrepare(rid, ts)                                 @*)
      (*@         } else if act == GPP_UNPREPARE {                                @*)
      (*@             gcoord.SendUnprepare(rid, ts)                               @*)
      (*@         } else if act == GPP_QUERY {                                    @*)
      (*@             gcoord.SendQuery(rid, ts)                                   @*)
      (*@         } else if act == GPP_REFRESH {                                  @*)
      (*@             // Keep sending keep-alive message until the transaction terminated. @*)
      (*@             gcoord.SendRefresh(rid, ts)                                 @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      (*@         if act == GPP_REFRESH {                                         @*)
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
      (*@                                                                         @*)
      case_bool_decide as Hfp; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendFastPrepare
                   with "Hlnrz Hsafepwrs Hsafeptgs Hptgs Hgcoord Hpwrs").
        { apply Hrid. }
        wp_pures.
        rewrite Hfp /=.
        case_bool_decide; first done.
        wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hvd; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendValidate
                   with "Hlnrz Hsafepwrs Hsafeptgs Hptgs Hgcoord Hpwrs").
        { apply Hrid. }
        wp_pures.
        rewrite Hvd /=.
        case_bool_decide; first done.
        wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hprep; wp_pures.
      { inv Hprep. destruct action; try done. simpl.
        wp_apply (wp_GroupCoordinator__SendPrepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_pures.
        wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hunprep; wp_pures.
      { inv Hunprep. destruct action; try done. simpl.
        wp_apply (wp_GroupCoordinator__SendUnprepare with "Hsafea Hgcoord").
        { apply Hrid. }
        wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hqr; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendQuery with "Hgcoord").
        { apply Hrid. }
        wp_pures.
        rewrite Hqr /=.
        case_bool_decide; first done.
        wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hrf; wp_pures.
      { wp_apply (wp_GroupCoordinator__SendRefresh with "Hgcoord").
        { apply Hrid. }
        wp_pures.
        rewrite Hrf /=.
        case_bool_decide; last done.
        wp_apply wp_Sleep. wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide; first done.
      wp_apply (wp_GroupCoordinator__waitOnResendSignal with "[$Hgcoord]").
      wp_pures.
      by iApply "HΦ".

      (*@     // The coordinator is no longer associated with @ts, this could happen only @*)
      (*@     // after the prepare decision for @ts on @rid is made. Hence, this session @*)
      (*@     // can terminate.                                                   @*)
      (*@ }                                                                       @*)
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
