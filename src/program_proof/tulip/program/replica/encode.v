From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  encode_string encode_version.

Section encode.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeTxnReadResponse
    (rid : u64) (ts : u64) (key : byte_string) (ver : dbpver) (slow : bool) :
    {{{ True }}}
      EncodeTxnReadResponse #ts #rid #(LitString key) (dbpver_to_val ver) #slow
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (ReadResp ts rid key ver slow) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnReadResponse(ts, rid uint64, key string, ver tulip.Version, slow bool) []byte { @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_READ)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rid)                                   @*)
    (*@     bs4 := util.EncodeString(bs3, key)                                  @*)
    (*@     bs5 := util.EncodeVersion(bs4, ver)                                 @*)
    (*@     data := marshal.WriteBool(bs5, slow)                                @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_EncodeVersion with "Hbs").
    iIntros (p5) "Hbs".
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (p6) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnFastPrepareResponse (ts : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnFastPrepareResponse #ts #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (FastPrepareResp ts rid res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnFastPrepareResponse(ts, rid, res uint64) []byte {         @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_FAST_PREPARE)                   @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rid)                                   @*)
    (*@     data := marshal.WriteInt(bs3, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnValidateResponse (ts : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnValidateResponse #ts #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (ValidateResp ts rid res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnValidateResponse(ts, rid, res uint64) []byte {            @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_VALIDATE)                       @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rid)                                   @*)
    (*@     data := marshal.WriteInt(bs3, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnPrepareResponse (ts : u64) (rank : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnPrepareResponse #ts #rank #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (PrepareResp ts rank rid res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnPrepareResponse(ts, rank, rid, res uint64) []byte {       @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_PREPARE)                        @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rank)                                  @*)
    (*@     bs4 := marshal.WriteInt(bs3, rid)                                   @*)
    (*@     data := marshal.WriteInt(bs4, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p5) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnUnprepareResponse (ts : u64) (rank : u64) (rid : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnUnprepareResponse #ts #rank #rid #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (UnprepareResp ts rank rid res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnUnprepareResponse(ts, rank, rid, res uint64) []byte {     @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_UNPREPARE)                      @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rank)                                  @*)
    (*@     bs4 := marshal.WriteInt(bs3, rid)                                   @*)
    (*@     data := marshal.WriteInt(bs4, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p4) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p5) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnQueryResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnQueryResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (QueryResp ts res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnQueryResponse(ts, res uint64) []byte {                    @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_QUERY)                          @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnCommitResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnCommitResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (CommitResp ts res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnCommitResponse(ts, res uint64) []byte {                   @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_COMMIT)                         @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnAbortResponse (ts : u64) (res : rpres) :
    {{{ True }}}
      EncodeTxnAbortResponse #ts #(rpres_to_u64 res)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnresp (AbortResp ts res) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnAbortResponse(ts, res uint64) []byte {                    @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_ABORT)                          @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, res)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p3) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

End encode.
