From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_read replica_fast_prepare replica_validate
  replica_prepare replica_unprepare replica_query replica_inquire
  replica_commit replica_abort encode decode.
From Perennial.program_proof.tulip.paxos Require Import base.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ, !paxos_ghostG Σ}.

  Theorem wp_Replica__RequestSession (rp : loc) (addr trml : chan) gid rid γ :
    is_replica_plus_network rp addr gid rid γ -∗
    {{{ True }}}
      Replica__RequestSession #rp (connection_socket addr trml)
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) RequestSession(conn grove_ffi.Connection) {          @*)
    (*@     for {                                                               @*)
    (*@         ret := grove_ffi.Receive(conn)                                  @*)
    (*@                                                                         @*)
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Receive.
    iNamed "Hrp".
    iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
    iApply ncfupd_mask_intro; first set_solver.
    iIntros "Hmask".
    iNamed "HinvnetO".
    assert (is_Some (listens !! addr)) as [msl Hmsl].
    { rewrite -elem_of_dom -Himgaddrm elem_of_map_img. by eauto. }
    iDestruct (big_sepM_lookup_acc with "Hlistens") as "[Hlst HlistensC]"; first apply Hmsl.
    iNamed "Hlst".
    iFrame "Hms".
    iIntros (err retdata) "[Hms Herr]".
    iDestruct ("HlistensC" with "[$Hms]") as "Hlistens"; first iFrame "# %".
    iMod "Hmask" as "_".
    iMod ("HinvnetC" with "[$Hlistens $Hconnects $Hterminals]") as "_"; first done.
    iIntros "!>" (retdataP) "Hretdata".

    (*@         if ret.Err {                                                    @*)
    (*@             break                                                       @*)
    (*@         }                                                               @*)
    (*@                                                                         @*)
    wp_pures.
    destruct err; wp_pures.
    { by iApply "HΦ". }
    iDestruct "Herr" as "%Hmsg".
    apply Henc in Hmsg as Hreq.
    destruct Hreq as (req & Hinreqs & Hreq). simpl in Hreq.

    (*@         req  := message.DecodeTxnRequest(ret.Data)                      @*)
    (*@         kind := req.Kind                                                @*)
    (*@         ts   := req.Timestamp                                           @*)
    (*@                                                                         @*)
    iDestruct (own_slice_to_small with "Hretdata") as "Hretdata".
    wp_apply (wp_DecodeTxnRequest with "Hretdata").
    { apply Hreq. }
    iIntros (pwrsP ptgsP) "Hpwrsptgs".
    assert (Hrid : rid ∈ rids_all).
    { apply elem_of_dom_2 in Haddr. by rewrite Hdomaddrm in Haddr. }
    iAssert (is_replica_gid_rid rp gid rid)%I as "Hgidrid".
    { by do 2 iNamed "Hrp". }
    iNamed "Hgidrid".
    destruct req; wp_pures.
    { (* Case: TxnRead. *)

      (*@         if kind == message.MSG_TXN_READ {                               @*)
      (*@             key := req.Key                                              @*)
      (*@             lts, value, ok := rp.Read(ts, key)                          @*)
      (*@             if !ok {                                                    @*)
      (*@                 // We can optionally respond with an error message to request @*)
      (*@                 // clients resending.                                   @*)
      (*@                 continue                                                @*)
      (*@             }                                                           @*)
      (*@             ver := tulip.Version{                                       @*)
      (*@                 Timestamp : lts,                                        @*)
      (*@                 Value     : value,                                      @*)
      (*@             }                                                           @*)
      (*@             data := message.EncodeTxnReadResponse(rp.rid, ts, key, ver) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iDestruct "Hsafe" as %(Hvts & Hvk & Hvg).
      iNamed "Hrp".
      wp_apply (wp_Replica__Read with "Hrp").
      { rewrite /valid_ts in Hvts. lia. }
      { apply Hvk. }
      { apply Hvg. }
      iIntros (lts value ok) "#Hread".
      wp_pures.
      destruct ok; wp_pures; last by iApply "HΦ".
      wp_loadField.
      wp_apply (wp_EncodeTxnReadResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := ReadResp _ _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnFastPrepare. *)

      (*@         } else if kind == message.MSG_TXN_FAST_PREPARE {                @*)
      (*@             pwrs := req.PartialWrites                                   @*)
      (*@             ptgs := req.ParticipantGroups                               @*)
      (*@             res := rp.FastPrepare(ts, pwrs, ptgs)                       @*)
      (*@             data := message.EncodeTxnFastPrepareResponse(rp.rid, ts, res) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iDestruct "Hpwrsptgs" as "[Hpwrs Hptgs]".
      iNamed "Hrp".
      iDestruct "Hsafe" as "(#Hlnrz & #Hsafepwrs & #Hsafeptgs)".
      wp_apply (wp_Replica__FastPrepare with "Hlnrz Hsafepwrs Hsafeptgs Hpwrs Hptgs Hrp").
      iIntros (res) "#Houtcome".
      wp_loadField.
      wp_apply (wp_EncodeTxnFastPrepareResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := FastPrepareResp _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnValidate. *)

      (*@         } else if kind == message.MSG_TXN_VALIDATE {                    @*)
      (*@             rank := req.Rank                                            @*)
      (*@             pwrs := req.PartialWrites                                   @*)
      (*@             ptgs := req.ParticipantGroups                               @*)
      (*@             res := rp.Validate(ts, rank, pwrs, ptgs)                    @*)
      (*@             data := message.EncodeTxnValidateResponse(ts, rp.rid, res)  @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iDestruct "Hpwrsptgs" as "[Hpwrs Hptgs]".
      iNamed "Hrp".
      iDestruct "Hsafe" as "(#Hlnrz & #Hsafepwrs & #Hsafeptgs)".
      wp_apply (wp_Replica__Validate with "Hlnrz Hsafepwrs Hsafeptgs Hpwrs Hptgs Hrp").
      iIntros (res) "#Houtcome".
      wp_loadField.
      wp_apply (wp_EncodeTxnValidateResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := ValidateResp _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnPrepare. *)

      (*@         } else if kind == message.MSG_TXN_PREPARE {                     @*)
      (*@             rank := req.Rank                                            @*)
      (*@             res := rp.Prepare(ts, rank)                                 @*)
      (*@             data := message.EncodeTxnPrepareResponse(rp.rid, ts, res)   @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iNamed "Hsafe".
      iNamed "Hrp".
      wp_apply (wp_Replica__Prepare with "Hpsl Hrp").
      { apply Hranknz. }
      iIntros (res) "#Houtcome".
      wp_loadField.
      wp_apply (wp_EncodeTxnPrepareResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := PrepareResp _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnUnprepare. *)

      (*@         } else if kind == message.MSG_TXN_UNPREPARE {                   @*)
      (*@             rank := req.Rank                                            @*)
      (*@             res := rp.Unprepare(ts, rank)                               @*)
      (*@             data := message.EncodeTxnUnprepareResponse(rp.rid, ts, res) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iNamed "Hsafe".
      iNamed "Hrp".
      wp_apply (wp_Replica__Unprepare with "Hpsl Hrp").
      { apply Hranknz. }
      iIntros (res) "#Houtcome".
      wp_loadField.
      wp_apply (wp_EncodeTxnUnprepareResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := UnprepareResp _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnQuery. *)

      (*@         } else if kind == message.MSG_TXN_QUERY {                       @*)
      (*@             rank := req.Rank                                            @*)
      (*@             res := rp.Query(ts, rank)                                   @*)
      (*@             data := message.EncodeTxnQueryResponse(ts, res)             @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iNamed "Hrp".
      wp_apply (wp_Replica__Query with "Hrp").
      iIntros (res) "#Houtcome".
      wp_pures.
      wp_apply (wp_EncodeTxnQueryResponse).
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := QueryResp _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnInquire. *)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iDestruct "Hsafe" as %[Hvts Hvrank].
      iNamed "Hrp".
      wp_apply (wp_Replica__Inquire with "Hrp").
      { apply Hvts. }
      { apply Hvrank. }
      clear pwrsP.
      iIntros (pp vd pwrsP res pwrs) "[#Houtcome #Hpwrs]".
      wp_pures.
      wp_loadField.
      wp_apply (wp_EncodeTxnInquireResponse with "Hpwrs").
      iIntros (dataP data) "[Hdata %Hdata]".
      wp_pures.
      (* Obtain [is_terminal γ trml] to respond to the sender. *)
      assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
      { rewrite elem_of_map. by exists (Message trml retdata). }
      iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
      (* Now send the message. *)
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_apply (wp_Send with "Hdata").
      clear Himgaddrm Hmsl Henc listens connects.
      iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
      iApply ncfupd_mask_intro; first set_solver.
      iIntros "Hmask".
      iNamed "HinvnetO".
      iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
      apply elem_of_dom in Hsend as [msc Hmsc].
      iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
      { apply Hmsc. }
      iNamed "Hconn".
      iFrame "Hms".
      iIntros (sent) "Hms".
      set msc' := if sent then _ else _.
      iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
      { iFrame "Hms".
        set resp := InquireResp _ _ _ _ _ _ _ _ in Hdata.
        destruct sent; last first.
        { iExists resps. iFrame "# %". }
        iExists ({[resp]} ∪ resps).
        iSplit.
        { iApply big_sepS_insert_2; [iFrame "# %" | done]. }
        iPureIntro.
        clear -Henc Hdata.
        set_solver.
      }
      iCombine "Hconn Hconnects" as "Hconnects".
      rewrite -(big_sepM_insert_delete _ _ trml msc').
      iMod "Hmask" as "_".
      iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
      { rewrite dom_insert_L.
        apply elem_of_dom_2 in Hmsc.
        replace (_ ∪ dom connects) with (dom connects) by set_solver.
        by iFrame "Hterminals".
      }
      iIntros "!>" (err) "Herr".
      wp_pures.
      by iApply "HΦ".
    }
    { (* Case: TxnInquire. *) by iApply "HΦ". }
    { (* Case: TxnCommit. *)

      (*@         } else if kind == message.MSG_TXN_COMMIT {                      @*)
      (*@             pwrs := req.PartialWrites                                   @*)
      (*@             ok := rp.Commit(ts, pwrs)                                   @*)
      (*@             if ok {                                                     @*)
      (*@                 data := message.EncodeTxnCommitResponse(ts, tulip.REPLICA_COMMITTED_TXN) @*)
      (*@                 grove_ffi.Send(conn, data)                              @*)
      (*@             } else {                                                    @*)
      (*@                 data := message.EncodeTxnCommitResponse(ts, tulip.REPLICA_WRONG_LEADER) @*)
      (*@                 grove_ffi.Send(conn, data)                              @*)
      (*@             }                                                           @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      iRename "Hpwrsptgs" into "Hpwrs".
      wp_apply (wp_Replica__Commit with "Hsafe Hpwrs Hrp").
      iIntros (ok) "_".
      wp_pures.
      destruct ok; wp_pures.
      { wp_apply (wp_EncodeTxnCommitResponse _ ReplicaCommittedTxn).
        iIntros (dataP data) "[Hdata %Hdata]".
        wp_pures.
        (* Obtain [is_terminal γ trml] to respond to the sender. *)
        assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
        { rewrite elem_of_map. by exists (Message trml retdata). }
        iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
        (* Now send the message. *)
        iDestruct (own_slice_to_small with "Hdata") as "Hdata".
        wp_apply (wp_Send with "Hdata").
        clear Himgaddrm Hmsl Henc listens connects.
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
        apply elem_of_dom in Hsend as [msc Hmsc].
        iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
        { apply Hmsc. }
        iNamed "Hconn".
        iFrame "Hms".
        iIntros (sent) "Hms".
        set msc' := if sent then _ else _.
        iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
        { iFrame "Hms".
          set resp := CommitResp _ _ in Hdata.
          destruct sent; last first.
          { iExists resps. iFrame "# %". }
          iExists ({[resp]} ∪ resps).
          iSplit.
          { by iApply big_sepS_insert_2. }
          iPureIntro.
          clear -Henc Hdata.
          set_solver.
        }
        iCombine "Hconn Hconnects" as "Hconnects".
        rewrite -(big_sepM_insert_delete _ _ trml msc').
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
        { rewrite dom_insert_L.
          apply elem_of_dom_2 in Hmsc.
          replace (_ ∪ dom connects) with (dom connects) by set_solver.
          by iFrame "Hterminals".
        }
        iIntros "!>" (err) "Herr".
        wp_pures.
        by iApply "HΦ".
      }
      { wp_apply (wp_EncodeTxnCommitResponse _ ReplicaWrongLeader).
        iIntros (dataP data) "[Hdata %Hdata]".
        wp_pures.
        (* Obtain [is_terminal γ trml] to respond to the sender. *)
        assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
        { rewrite elem_of_map. by exists (Message trml retdata). }
        iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
        (* Now send the message. *)
        iDestruct (own_slice_to_small with "Hdata") as "Hdata".
        wp_apply (wp_Send with "Hdata").
        clear Himgaddrm Hmsl Henc listens connects.
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
        apply elem_of_dom in Hsend as [msc Hmsc].
        iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
        { apply Hmsc. }
        iNamed "Hconn".
        iFrame "Hms".
        iIntros (sent) "Hms".
        set msc' := if sent then _ else _.
        iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
        { iFrame "Hms".
          set resp := CommitResp _ _ in Hdata.
          destruct sent; last first.
          { iExists resps. iFrame "# %". }
          iExists ({[resp]} ∪ resps).
          iSplit.
          { by iApply big_sepS_insert_2. }
          iPureIntro.
          clear -Henc Hdata.
          set_solver.
        }
        iCombine "Hconn Hconnects" as "Hconnects".
        rewrite -(big_sepM_insert_delete _ _ trml msc').
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
        { rewrite dom_insert_L.
          apply elem_of_dom_2 in Hmsc.
          replace (_ ∪ dom connects) with (dom connects) by set_solver.
          by iFrame "Hterminals".
        }
        iIntros "!>" (err) "Herr".
        wp_pures.
        by iApply "HΦ".
      }
    }
    { (* Case: TxnAbort. *)

      (*@         } else if kind == message.MSG_TXN_ABORT {                       @*)
      (*@             ok := rp.Abort(ts)                                          @*)
      (*@             if ok {                                                     @*)
      (*@                 data := message.EncodeTxnAbortResponse(ts, tulip.REPLICA_ABORTED_TXN) @*)
      (*@                 grove_ffi.Send(conn, data)                              @*)
      (*@             } else {                                                    @*)
      (*@                 data := message.EncodeTxnAbortResponse(ts, tulip.REPLICA_WRONG_LEADER) @*)
      (*@                 grove_ffi.Send(conn, data)                              @*)
      (*@             }                                                           @*)
      (*@         }                                                               @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      wp_apply (wp_Replica__Abort with "Hsafe Hrp").
      iIntros (ok) "_".
      wp_pures.
      destruct ok; wp_pures.
      { wp_apply (wp_EncodeTxnAbortResponse _ ReplicaAbortedTxn).
        iIntros (dataP data) "[Hdata %Hdata]".
        wp_pures.
        (* Obtain [is_terminal γ trml] to respond to the sender. *)
        assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
        { rewrite elem_of_map. by exists (Message trml retdata). }
        iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
        (* Now send the message. *)
        iDestruct (own_slice_to_small with "Hdata") as "Hdata".
        wp_apply (wp_Send with "Hdata").
        clear Himgaddrm Hmsl Henc listens connects.
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
        apply elem_of_dom in Hsend as [msc Hmsc].
        iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
        { apply Hmsc. }
        iNamed "Hconn".
        iFrame "Hms".
        iIntros (sent) "Hms".
        set msc' := if sent then _ else _.
        iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
        { iFrame "Hms".
          set resp := AbortResp _ _ in Hdata.
          destruct sent; last first.
          { iExists resps. iFrame "# %". }
          iExists ({[resp]} ∪ resps).
          iSplit.
          { by iApply big_sepS_insert_2. }
          iPureIntro.
          clear -Henc Hdata.
          set_solver.
        }
        iCombine "Hconn Hconnects" as "Hconnects".
        rewrite -(big_sepM_insert_delete _ _ trml msc').
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
        { rewrite dom_insert_L.
          apply elem_of_dom_2 in Hmsc.
          replace (_ ∪ dom connects) with (dom connects) by set_solver.
          by iFrame "Hterminals".
        }
        iIntros "!>" (err) "Herr".
        wp_pures.
        by iApply "HΦ".
      }
      { wp_apply (wp_EncodeTxnAbortResponse _ ReplicaWrongLeader).
        iIntros (dataP data) "[Hdata %Hdata]".
        wp_pures.
        (* Obtain [is_terminal γ trml] to respond to the sender. *)
        assert (Htrml : trml ∈ (set_map msg_sender msl : gset chan)).
        { rewrite elem_of_map. by exists (Message trml retdata). }
        iDestruct (big_sepS_elem_of with "Hsender") as "Htrml"; first apply Htrml.
        (* Now send the message. *)
        iDestruct (own_slice_to_small with "Hdata") as "Hdata".
        wp_apply (wp_Send with "Hdata").
        clear Himgaddrm Hmsl Henc listens connects.
        iInv "Hinvnet" as "> HinvnetO" "HinvnetC".
        iApply ncfupd_mask_intro; first set_solver.
        iIntros "Hmask".
        iNamed "HinvnetO".
        iDestruct (terminal_lookup with "Htrml Hterminals") as %Hsend.
        apply elem_of_dom in Hsend as [msc Hmsc].
        iDestruct (big_sepM_delete with "Hconnects") as "[Hconn Hconnects]".
        { apply Hmsc. }
        iNamed "Hconn".
        iFrame "Hms".
        iIntros (sent) "Hms".
        set msc' := if sent then _ else _.
        iAssert (connect_inv trml msc' gid γ)%I with "[Hms]" as "Hconn".
        { iFrame "Hms".
          set resp := AbortResp _ _ in Hdata.
          destruct sent; last first.
          { iExists resps. iFrame "# %". }
          iExists ({[resp]} ∪ resps).
          iSplit.
          { by iApply big_sepS_insert_2. }
          iPureIntro.
          clear -Henc Hdata.
          set_solver.
        }
        iCombine "Hconn Hconnects" as "Hconnects".
        rewrite -(big_sepM_insert_delete _ _ trml msc').
        iMod "Hmask" as "_".
        iMod ("HinvnetC" with "[$Hlistens $Hconnects Hterminals]") as "_".
        { rewrite dom_insert_L.
          apply elem_of_dom_2 in Hmsc.
          replace (_ ∪ dom connects) with (dom connects) by set_solver.
          by iFrame "Hterminals".
        }
        iIntros "!>" (err) "Herr".
        wp_pures.
        by iApply "HΦ".
      }
    }
  Qed.

End program.
