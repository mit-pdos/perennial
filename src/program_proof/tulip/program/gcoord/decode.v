From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  decode_string decode_version.


Definition txnresp_to_val (resp : txnresp) (entsP : Slice.t) : val :=
  match resp with
  | ReadResp ts rid key ver slow =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 100)); ("Timestamp", #ts); ("ReplicaID", #rid);
          ("Key", #(LitString key)); ("Version", dbpver_to_val ver); ("Slow", #slow)]
  | FastPrepareResp ts rid res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 201)); ("Timestamp", #ts); ("ReplicaID", #rid);
          ("Result", #(rpres_to_u64 res))]
  | ValidateResp ts rid res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 202)); ("Timestamp", #ts); ("ReplicaID", #rid);
          ("Result", #(rpres_to_u64 res))]
  | PrepareResp ts rank rid res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 203)); ("Timestamp", #ts); ("Rank", #rank);
          ("ReplicaID", #rid); ("Result", #(rpres_to_u64 res))]
  | UnprepareResp ts rank rid res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 204)); ("Timestamp", #ts); ("Rank", #rank);
          ("ReplicaID", #rid); ("Result", #(rpres_to_u64 res))]
  | QueryResp ts res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 205)); ("Timestamp", #ts); ("Result", #(rpres_to_u64 res))]
  | CommitResp ts res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 300)); ("Timestamp", #ts); ("Result", #(rpres_to_u64 res))]
  | AbortResp ts res =>
      struct.mk_f TxnResponse [
          ("Kind", #(U64 301)); ("Timestamp", #ts); ("Result", #(rpres_to_u64 res))]
  end.

Section decode.
  Context `{!heapGS Σ, !tulip_ghostG Σ}.

  Theorem wp_DecodeTxnReadResponse (bsP : Slice.t) ts rid key ver slow :
    let bs := encode_read_resp_xkind ts rid key ver slow in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnReadResponse (to_val bsP)
    {{{ RET (txnresp_to_val (ReadResp ts rid key ver slow) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnReadResponse(bs []byte) TxnResponse {                     @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     rid, bs2 := marshal.ReadInt(bs1)                                    @*)
    (*@     key, bs3 := util.DecodeString(bs2)                                  @*)
    (*@     ver, bs4 := util.DecodeVersion(bs3)                                 @*)
    (*@     slow, _ := marshal.ReadBool(bs4)                                    @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_READ,                                       @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         ReplicaID : rid,                                                @*)
    (*@         Key       : key,                                                @*)
    (*@         Version   : ver,                                                @*)
    (*@         Slow      : slow,                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_DecodeString with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_DecodeVersion with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_ReadBool with "Hbs").
    iIntros (b p5) "[%Hb Hbs]".
    wp_pures.
    rewrite Hb.
    by destruct slow; iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnFastPrepareResponse (bsP : Slice.t) ts rid res :
    let bs := encode_ts_rid_res ts rid res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnFastPrepareResponse (to_val bsP)
    {{{ RET (txnresp_to_val (FastPrepareResp ts rid res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnFastPrepareResponse(bs []byte) TxnResponse {              @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     rid, bs2 := marshal.ReadInt(bs1)                                    @*)
    (*@     res, _ := marshal.ReadInt(bs2)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_FAST_PREPARE,                               @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         ReplicaID : rid,                                                @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnValidateResponse (bsP : Slice.t) ts rid res :
    let bs := encode_ts_rid_res ts rid res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnValidateResponse (to_val bsP)
    {{{ RET (txnresp_to_val (ValidateResp ts rid res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnValidateResponse(bs []byte) TxnResponse {                 @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     rid, bs2 := marshal.ReadInt(bs1)                                    @*)
    (*@     res, _ := marshal.ReadInt(bs2)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_VALIDATE,                                   @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         ReplicaID : rid,                                                @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnPrepareResponse (bsP : Slice.t) ts rank rid res :
    let bs := encode_ts_rank_rid_res ts rank rid res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnPrepareResponse (to_val bsP)
    {{{ RET (txnresp_to_val (PrepareResp ts rank rid res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnPrepareResponse(bs []byte) TxnResponse {                  @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     rank, bs2 := marshal.ReadInt(bs1)                                   @*)
    (*@     rid, bs3 := marshal.ReadInt(bs2)                                    @*)
    (*@     res, _ := marshal.ReadInt(bs3)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_PREPARE,                                    @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Rank      : rank,                                               @*)
    (*@         ReplicaID : rid,                                                @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnUnprepareResponse (bsP : Slice.t) ts rank rid res :
    let bs := encode_ts_rank_rid_res ts rank rid res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnUnprepareResponse (to_val bsP)
    {{{ RET (txnresp_to_val (UnprepareResp ts rank rid res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnUnprepareResponse(bs []byte) TxnResponse {                @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     rank, bs2 := marshal.ReadInt(bs1)                                   @*)
    (*@     rid, bs3 := marshal.ReadInt(bs2)                                    @*)
    (*@     res, _ := marshal.ReadInt(bs3)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_UNPREPARE,                                  @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Rank      : rank,                                               @*)
    (*@         ReplicaID : rid,                                                @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnQueryResponse (bsP : Slice.t) ts res :
    let bs := encode_ts_res ts res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnQueryResponse (to_val bsP)
    {{{ RET (txnresp_to_val (QueryResp ts res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnQueryResponse(bs []byte) TxnResponse {                    @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     res, _ := marshal.ReadInt(bs1)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_QUERY,                                      @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnCommitResponse (bsP : Slice.t) ts res :
    let bs := encode_ts_res ts res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnCommitResponse (to_val bsP)
    {{{ RET (txnresp_to_val (CommitResp ts res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnCommitResponse(bs []byte) TxnResponse {                   @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     res, _ := marshal.ReadInt(bs1)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_COMMIT,                                     @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnAbortResponse (bsP : Slice.t) ts res :
    let bs := encode_ts_res ts res in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnAbortResponse (to_val bsP)
    {{{ RET (txnresp_to_val (AbortResp ts res) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnAbortResponse(bs []byte) TxnResponse {                    @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     res, _ := marshal.ReadInt(bs1)                                      @*)
    (*@     return TxnResponse{                                                 @*)
    (*@         Kind      : MSG_TXN_ABORT,                                      @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Result    : res,                                                @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeTxnResponse (bsP : Slice.t) (resp : txnresp) :
    let bs := encode_txnresp resp in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeTxnResponse (to_val bsP)
    {{{ (entsP : Slice.t), RET (txnresp_to_val resp entsP);
        (* TODO: this will be used after adding backup coordinator *)
        match resp with
        | _ => True
        end
    }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeTxnResponse(bs []byte) TxnResponse {                         @*)
    (*@     kind, bs1 := marshal.ReadInt(bs)                                    @*)
    (*@     if kind == MSG_TXN_READ {                                           @*)
    (*@         return DecodeTxnReadResponse(bs1)                               @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_FAST_PREPARE {                                   @*)
    (*@         return DecodeTxnFastPrepareResponse(bs1)                        @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_VALIDATE {                                       @*)
    (*@         return DecodeTxnValidateResponse(bs1)                           @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_PREPARE {                                        @*)
    (*@         return DecodeTxnPrepareResponse(bs1)                            @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_UNPREPARE {                                      @*)
    (*@         return DecodeTxnUnprepareResponse(bs1)                          @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_QUERY {                                          @*)
    (*@         return DecodeTxnQueryResponse(bs1)                              @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_COMMIT {                                         @*)
    (*@         return DecodeTxnCommitResponse(bs1)                             @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_TXN_ABORT {                                          @*)
    (*@         return DecodeTxnAbortResponse(bs1)                              @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct resp; wp_pures.
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnReadResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnFastPrepareResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnValidateResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnPrepareResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnUnprepareResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnQueryResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnCommitResponse with "Hbs").
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeTxnAbortResponse with "Hbs").
      by iApply "HΦ".
    }

    (*@     return TxnResponse{}                                                @*)
    (*@ }                                                                       @*)
  Qed.

End decode.
