From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.gcoord Require Import decode.
From Perennial.program_proof.tulip.program.backup Require Import
  bgcoord_repr bgpreparer_repr bgcoord_receive
  bgpreparer_process_inquire_result bgpreparer_process_validate_result
  bgpreparer_process_prepare_result bgpreparer_process_unprepare_result
  bgpreparer_process_finalization_result.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_BackupGroupCoordinator__ResponseSession
    (gcoord : loc) (rid : u64) (addr : chan) (addrm : gmap u64 chan) rk ts gid γ :
    addrm !! rid = Some addr ->
    is_backup_gcoord_with_addrm gcoord addrm rk ts gid γ -∗
    {{{ True }}}
      BackupGroupCoordinator__ResponseSession #gcoord #rid
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Haddr) "#Hgcoord".
    iIntros (Φ) "!> _ HΦ".
    wp_rec.
    

    (*@ func (gcoord *BackupGroupCoordinator) ResponseSession(rid uint64) {     @*)
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
    wp_apply (wp_BackupGroupCoordinator__Receive with "Hgcoord").
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
    iIntros (pwrsP) "Hpwrs".
    wp_pures.

    (*@         if gcoord.ts != msg.Timestamp {                                 @*)
    (*@             continue                                                    @*)
    (*@         }                                                               @*)
    (*@         gcoord.mu.Lock()                                                @*)
    (*@         gpp := gcoord.gpp                                               @*)
    (*@         if kind == message.MSG_TXN_INQUIRE {                            @*)
    (*@             // This is a proof artifact since any message received in this @*)
    (*@             // session should be delivered to @gcoord.cid.              @*)
    (*@             if gcoord.cid == msg.CoordID {                              @*)
    (*@                 pp := tulip.PrepareProposal{                            @*)
    (*@                     Rank     : msg.Rank,                                @*)
    (*@                     Prepared : msg.Prepared,                            @*)
    (*@                 }                                                       @*)
    (*@                 gpp.processInquireResult(msg.ReplicaID, pp, msg.Validated, msg.PartialWrites, msg.Result) @*)
    (*@             }                                                           @*)
    (*@         } else if kind == message.MSG_TXN_VALIDATE {                    @*)
    (*@             gpp.processValidateResult(msg.ReplicaID, msg.Result)        @*)
    (*@         } else if kind == message.MSG_TXN_PREPARE {                     @*)
    (*@             gpp.processPrepareResult(msg.ReplicaID, msg.Result)         @*)
    (*@         } else if kind == message.MSG_TXN_UNPREPARE {                   @*)
    (*@             gpp.processUnprepareResult(msg.ReplicaID, msg.Result)       @*)
    (*@         } else if kind == message.MSG_TXN_REFRESH {                     @*)
    (*@             // No reponse message for REFRESH.                          @*)
    (*@         } else if kind == message.MSG_TXN_COMMIT || kind == message.MSG_TXN_ABORT { @*)
    (*@             // Not using msg.Timestamp might be an issue in the proof without an @*)
    (*@             // invariant saying that message sent through this connection can @*)
    (*@             // only be of that of the transaction we're finalizing here. @*)
    (*@             gpp.processFinalizationResult(msg.Result)                   @*)
    (*@         }                                                               @*)
    (*@         // In the current design the coordinator will be notified whenever a new @*)
    (*@         // response arrives, and then checks whether the final result (e.g., @*)
    (*@         // prepared, committed, or aborted in the case of preparing) is @*)
    (*@         // ready. An optimization would be requiring those @process{X}Result @*)
    (*@         // functions to return a bool indicating the final result is ready, and @*)
    (*@         // call @gcoord.cv.Signal only on those occasions.              @*)
    (*@         gcoord.cv.Signal()                                              @*)
    (*@         gcoord.mu.Unlock()                                              @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    clear Haddr rid.
    destruct resp; wp_pures.
    { (* Case: Read. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: FastPrepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Validate. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      iNamed "Hresp".
      wp_apply (wp_BackupGroupPreparer__processValidateResult with "Hsafe Hinv Hgpp").
      { apply Hrk. }
      { apply Hrid. }
      { apply Hgid. }
      iIntros "Hgpp".
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Prepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_loadField.
      wp_pures.
      case_bool_decide as Hrank; wp_pures.
      { inv Hrank.
        iNamed "Hresp".
        wp_apply (wp_BackupGroupPreparer__processPrepareResult with "Hsafe Hgpp").
        { apply Hrk. }
        { apply Hrid. }
        iIntros "Hgpp".
        wp_loadField.
        wp_apply (wp_Cond__Signal with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Unprepare. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_loadField.
      wp_pures.
      case_bool_decide as Hrank; wp_pures.
      { inv Hrank.
        iNamed "Hresp".
        wp_apply (wp_BackupGroupPreparer__processUnprepareResult with "Hsafe Hgpp").
        { apply Hrk. }
        { apply Hrid. }
        iIntros "Hgpp".
        wp_loadField.
        wp_apply (wp_Cond__Signal with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Query. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Inquire. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      do 2 wp_loadField. wp_pures.
      case_bool_decide; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Cond__Signal with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField. wp_pures.
      case_bool_decide; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Cond__Signal with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      wp_loadField. wp_pures.
      case_bool_decide; wp_pures; last first.
      { wp_loadField.
        wp_apply (wp_Cond__Signal with "Hcv").
        wp_loadField.
        wp_apply (wp_Mutex__Unlock with "[-HΦ]").
        { by iFrame "Hlock Hlocked ∗". }
        wp_pures.
        by iApply "HΦ".
      }
      inv H.
      assert (cid0 = cid) as ->.
      { destruct cid0 as [r0 g0].
        destruct cid as [r g].
        simpl in H0, H3. by subst.
      }
      iNamed "Hresp".
      wp_apply (wp_BackupGroupPreparer__processInquireResult with "Hpwrs Hsafe Hinv Hgpp").
      { apply Hrk. }
      { apply Hrid. }
      { apply Hgid. }
      iIntros "Hgpp".
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Commit. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_apply (wp_BackupGroupPreparer__processFinalizationResult with "Hgpp").
      iIntros "Hgpp".
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: Abort. *)
      iNamed "Hgcoord".
      wp_loadField.
      wp_pures.
      case_bool_decide as Htseq; wp_pures; last by iApply "HΦ".
      symmetry in Htseq. inv Htseq.
      wp_loadField.
      wp_apply (wp_Mutex__Lock with "Hlock").
      iIntros "[Hlocked Hgcoord]".
      iNamed "Hgcoord". iNamed "Hgpp".
      wp_loadField.
      wp_pures.
      wp_apply (wp_BackupGroupPreparer__processFinalizationResult with "Hgpp").
      iIntros "Hgpp".
      wp_loadField.
      wp_apply (wp_Cond__Signal with "Hcv").
      wp_loadField.
      wp_apply (wp_Mutex__Unlock with "[-HΦ]").
      { by iFrame "Hlock Hlocked ∗". }
      wp_pures.
      by iApply "HΦ".
    }
  Qed.

End program.
