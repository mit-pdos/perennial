From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.replica Require Import
  replica_repr replica_read replica_fast_prepare replica_validate
  replica_prepare replica_unprepare replica_query replica_commit replica_abort.

Definition txnreq_to_val (req : txnreq) (pwrsP : Slice.t) : val :=
  match req with
  | ReadReq ts key =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 100)); ("Timestamp", #ts); ("Key", #(LitString key))]
  | FastPrepareReq ts pwrs =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 201)); ("Timestamp", #ts); ("PartialWrites", to_val pwrsP)]
  | ValidateReq ts rank pwrs =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 202)); ("Timestamp", #ts); ("Rank", #rank);
          ("PartialWrites", to_val pwrsP)]
  | PrepareReq ts rank =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 203)); ("Timestamp", #ts); ("Rank", #rank)]
  | UnprepareReq ts rank =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 204)); ("Timestamp", #ts); ("Rank", #rank)]
  | QueryReq ts rank =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 205)); ("Timestamp", #ts); ("Rank", #rank)]
  | RefreshReq ts rank =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 210)); ("Timestamp", #ts); ("Rank", #rank)]
  | CommitReq ts pwrs =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 300)); ("Timestamp", #ts); ("PartialWrites", to_val pwrsP)]
  | AbortReq ts =>
      struct.mk_f TxnRequest [
          ("Kind", #(U64 301)); ("Timestamp", #ts)]
  end.

Section decode.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_DecodeTxnRequest (dataP : Slice.t) (data : list u8) (req : txnreq) :
    data = encode_txnreq req ->
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
      DecodeTxnRequest (to_val dataP)
    {{{ (pwrsP : Slice.t), RET (txnreq_to_val req pwrsP);
        match req with
        | FastPrepareReq _ pwrs => (∃ pwrsL, own_dbmap_in_slice pwrsP pwrsL pwrs)
        | ValidateReq _ _ pwrs => (∃ pwrsL, own_dbmap_in_slice pwrsP pwrsL pwrs)
        | CommitReq _ pwrs => (∃ pwrsL, own_dbmap_in_slice pwrsP pwrsL pwrs)
        | _ => True
        end
    }}}.
  Proof.
    iIntros (Hdataenc Φ) "Hdata HΦ".
    wp_rec.
  Admitted.

End decode.

Section encode.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeTxnReadResponse
    (rid : u64) (ts : u64) (key : string) (lts : u64) (value : dbval) :
    {{{ True }}}
      EncodeTxnReadResponse #rid #ts #(LitString key) #lts (dbval_to_val value)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (ReadResp rid ts key (lts, value))⌝
    }}}.
  Proof.
  Admitted.

  Theorem wp_EncodeTxnFastPrepareResponse (ts : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnFastPrepareResponse #ts #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (FastPrepareResp ts rid res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnFastPrepareResponse(ts, rid, res uint64) []byte {         @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnValidateResponse (ts : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnValidateResponse #ts #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (ValidateResp ts rid res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnValidateResponse(ts, rid, res uint64) []byte {            @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnPrepareResponse (ts : u64) (rank : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnPrepareResponse #ts #rank #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (PrepareResp ts rank rid res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnPrepareResponse(ts, rank, rid, res uint64) []byte {       @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnUnprepareResponse (ts : u64) (rank : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnUnprepareResponse #ts #rank #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (UnprepareResp ts rank rid res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnUnprepareResponse(ts, rank, rid, res uint64) []byte {     @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnQueryResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnQueryResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (QueryResp ts res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnQueryResponse(ts, res uint64) []byte {                    @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnCommitResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnCommitResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (CommitResp ts res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnCommitResponse(ts, res uint64) []byte {                   @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

  Theorem wp_EncodeTxnAbortResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnAbortResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_txnresp (AbortResp ts res)⌝
    }}}.
  Proof.
    (*@ func EncodeTxnAbortResponse(ts, res uint64) []byte {                    @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

End encode.

Section program.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

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
    assert (∃ req, retdata = encode_txnreq req ∧ req ∈ reqs) as (req & Hreq & Hinreqs).
    { specialize (Henc retdata).
      apply (elem_of_map_2 msg_data (D := gset (list u8))) in Hmsg.
      specialize (Henc Hmsg).
      by rewrite elem_of_map in Henc.
    }

    (*@         req  := message.DecodeTxnRequest(ret.Data)                      @*)
    (*@         kind := req.Kind                                                @*)
    (*@         ts   := req.Timestamp                                           @*)
    (*@                                                                         @*)
    wp_apply (wp_DecodeTxnRequest with "Hretdata").
    { apply Hreq. }
    iIntros (entsaP) "Hentsa".
    assert (Hrid : rid ∈ rids_all).
    { apply elem_of_dom_2 in Haddr. by rewrite Hdomaddrm in Haddr. }
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
        set resp := ReadResp _ _ _ _ in Hdata.
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
      (*@             res := rp.FastPrepare(ts, pwrs, nil)                        @*)
      (*@             data := message.EncodeTxnFastPrepareResponse(rp.rid, ts, res) @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      simpl.
      iDestruct "Hentsa" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__FastPrepare with "Hsafe Hrp Hpwrs").
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
      (*@             pwrs := req.PartialWrites                                   @*)
      (*@             rank := req.Rank                                            @*)
      (*@             res := rp.Validate(ts, rank, pwrs, nil)                     @*)
      (*@             data := message.EncodeTxnValidateResponse(rp.rid, ts, res)  @*)
      (*@             grove_ffi.Send(conn, data)                                  @*)
      (*@                                                                         @*)
      iDestruct (big_sepS_elem_of with "Hreqs") as "Hsafe"; first apply Hinreqs.
      simpl.
      iDestruct "Hentsa" as (pwrsL) "Hpwrs".
      wp_apply (wp_Replica__Validate with "Hsafe Hrp Hpwrs").
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
    { (* Case: TxnRefresh. *) by iApply "HΦ". }
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
      wp_apply (wp_Replica__Commit with "Hsafe Hrp Hentsa").
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

  Theorem wp_Replica__Serve (rp : loc) addr gid rid γ :
    is_replica_plus_network rp addr gid rid γ -∗
    {{{ True }}}
      Replica__Serve #rp
    {{{ RET #(); True }}}.
  Proof.
    iIntros "#Hrp" (Φ) "!> _ HΦ".
    wp_rec.

    (*@ func (rp *Replica) Serve() {                                            @*)
    (*@     ls := grove_ffi.Listen(rp.addr)                                     @*)
    (*@     for {                                                               @*)
    (*@         conn := grove_ffi.Accept(ls)                                    @*)
    (*@         go func() {                                                     @*)
    (*@             rp.RequestSession(conn)                                     @*)
    (*@         }()                                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    iNamed "Hrp".
    wp_loadField.
    wp_apply wp_Listen.
    wp_pures.
    wp_apply (wp_forBreak (λ _, True)%I); wp_pures; last by iApply "HΦ".
    clear Φ.
    iIntros (Φ) "!> _ HΦ".
    wp_pures.
    wp_apply wp_Accept.
    iIntros (chanpeer) "_".
    wp_pures.
    wp_apply (wp_fork).
    { (* Fork. *)
      wp_apply wp_Replica__RequestSession.
      { iFrame "# %". }
      done.
    }
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
