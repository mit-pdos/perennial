From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import
  gcoord_repr greader_repr gpreparer_repr
  gcoord_attached_with gcoord_receive gcoord_process_finalization_result
  greader_process_read_result gpreparer_process_fast_prepare_result
  gpreparer_process_validate_result gpreparer_process_prepare_result
  gpreparer_process_unprepare_result gpreparer_process_query_result
  decode.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_GroupCoordinator__ResponseSession
    (gcoord : loc) (rid : u64) (addr : chan) (addrm : gmap u64 chan) gid γ :
    addrm !! rid = Some addr ->
    is_gcoord_with_addrm gcoord gid addrm γ -∗
    {{{ True }}}
      GroupCoordinator__ResponseSession #gcoord #rid
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddr) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (gcoord *GroupCoordinator) ResponseSession(rid uint64) {           @*)
    (*@     for {                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.

    (*@         data, ok := gcoord.Receive(rid)                                 @*)
    (*@         if !ok {                                                        @*)
    (*@             // Try to re-establish a connection on failure.             @*)
    (*@             primitive.Sleep(params.NS_RECONNECT)                        @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_apply (wp_GroupCoordinator__Receive with "Hgcoord").
    { apply Haddr. }
    iIntros (dataP ok) "Hdata".
    wp_pures.
    destruct ok; wp_pures; last first.
    { wp_apply wp_Sleep.
      wp_pures.
      by iApply "HΦ".
    }
    iDestruct "Hdata" as (data resp) "(Hdata & #Hresp & %Hdataenc)".

    (*@         msg := message.DecodeTxnResponse(data)                          @*)
    (*@         kind := msg.Kind                                                @*)
    (*@                                                                         @*)
    iDestruct (own_slice_to_small with "Hdata") as "Hdata".
    wp_apply (wp_DecodeTxnResponse with "Hdata").
    { apply Hdataenc. }
    iIntros (entsP) "Hents".

    (*@         gcoord.mu.Lock()                                                @*)
    (*@                                                                         @*)
    (*@         // Handle commit and abort responses. Note that timestamp check should @*)
    (*@         // happen after.                                                @*)
    (*@         if kind == message.MSG_TXN_COMMIT || kind == message.MSG_TXN_ABORT { @*)
    (*@             gcoord.processFinalizationResult(msg.Timestamp, msg.Result) @*)
    (*@             gcoord.mu.Unlock()                                          @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         // Ignore this response message if it is not the currently active one. @*)
    (*@         if !gcoord.attachedWith(msg.Timestamp) {                        @*)
    (*@             gcoord.mu.Unlock()                                          @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         if kind == message.MSG_TXN_READ {                               @*)
    (*@             gcoord.grd.processReadResult(msg.ReplicaID, msg.Key, msg.Version) @*)
    (*@         } else if kind == message.MSG_TXN_FAST_PREPARE {                @*)
    (*@             gcoord.gpp.processFastPrepareResult(msg.ReplicaID, msg.Result) @*)
    (*@         } else if kind == message.MSG_TXN_VALIDATE {                    @*)
    (*@             gcoord.gpp.processValidateResult(msg.ReplicaID, msg.Result) @*)
    (*@         } else if kind == message.MSG_TXN_PREPARE {                     @*)
    (*@             gcoord.gpp.processPrepareResult(msg.ReplicaID, msg.Result)  @*)
    (*@         } else if kind == message.MSG_TXN_UNPREPARE {                   @*)
    (*@             gcoord.gpp.processUnprepareResult(msg.ReplicaID, msg.Result) @*)
    (*@         } else if kind == message.MSG_TXN_QUERY {                       @*)
    (*@             gcoord.gpp.processQueryResult(msg.ReplicaID, msg.Result)    @*)
    (*@         } else if kind == message.MSG_TXN_REFRESH {                     @*)
    (*@             // No reponse message for REFRESH.                          @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    (*@         // In the current design the coordinator will be notified whenever a new @*)
    (*@         // response arrives, and then checks whether the final result (e.g., @*)
    (*@         // prepared, committed, or aborted in the case of preparing) is @*)
    (*@         // ready. An optimization would be requiring those @process{X}Result @*)
    (*@         // functions to return a bool indicating the final result is ready, and @*)
    (*@         // call @gcoord.cv.Signal only on those occasions.              @*)
    (*@         gcoord.cv.Broadcast()                                           @*)
    (*@                                                                         @*)
    (*@         gcoord.mu.Unlock()                                              @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    clear Haddr rid.
    destruct resp; wp_pures.
    { (* Case: TxnRead. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.
      iNamed "Hgcoord". iNamed "Hgrd".
      wp_loadField.
      iNamed "Hresp".
      wp_apply (wp_GroupReader__processReadResult with "Hsafe Hgrd").
      { apply Hrid. }
      iIntros "Hgrd".
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnFastPrepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      iNamed "Hresp".
      wp_apply (wp_GroupPreparer__processFastPrepareResult with "Hsafe Hinv Hgpp").
      { apply Hgid. }
      { apply Hrid. }
      iIntros (resend) "Hgpp".
      wp_pures.
      destruct resend; wp_pures.
      { wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcvrs").
        wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnValdiate. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      iNamed "Hresp".
      wp_apply (wp_GroupPreparer__processValidateResult with "Hsafe Hinv Hgpp").
      { apply Hgid. }
      { apply Hrid. }
      iIntros (resend) "Hgpp".
      destruct resend; wp_pures.
      { wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcvrs").
        wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnPrepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hrank; wp_pures.
      { inv Hrank.
        iNamed "Hgcoord". iNamed "Hgpp".
        wp_loadField.
        iNamed "Hresp".
        wp_apply (wp_GroupPreparer__processPrepareResult with "Hsafe Hgpp").
        { apply Hrid. }
        iIntros "Hgpp".
        wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnUnprepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      case_bool_decide as Hrank; wp_pures.
      { inv Hrank.
        iNamed "Hgcoord". iNamed "Hgpp".
        wp_loadField.
        iNamed "Hresp".
        wp_apply (wp_GroupPreparer__processUnprepareResult with "Hsafe Hgpp").
        { apply Hrid. }
        iIntros "Hgpp".
        wp_loadField.
        wp_apply (wp_Cond__Broadcast with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnQuery. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      iNamed "Hresp".
      wp_apply (wp_GroupPreparer__processQueryResult with "Hresp Hgpp").
      iIntros "Hgpp".
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnInquire. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 2 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__attachedWith with "Hgcoord").
      iIntros (attached) "Hgcoord".
      wp_pures.
      destruct attached; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_pures.
      iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Cond__Broadcast with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 3 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__processFinalizationResult with "Hgfl").
      iIntros "Hgfl".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { iNamed "Hgcoord".
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      wp_pures.
      do 3 iNamed "Hgcoord".
      wp_apply (wp_GroupCoordinator__processFinalizationResult with "Hgfl").
      iIntros "Hgfl".
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End program.
