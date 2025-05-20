From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import
  encode_string encode_kvmap encode_ints.

Opaque u64_le.

Section encode.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeTxnReadRequest (ts : u64) (key : byte_string) :
    {{{ True }}}
      EncodeTxnReadRequest #ts #(LitString key)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (ReadReq ts key) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnReadRequest(ts uint64, key byte_string) []byte {               @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_READ)                           @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := util.EncodeString(bs2, key)                                 @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnFastPrepareRequest
    (ts : u64) (pwrsP : loc) (ptgsP : Slice.t) q (pwrs : dbmap) (ptgs : txnptgs) :
    is_txnptgs_in_slice ptgsP ptgs -∗
    {{{ own_map pwrsP q pwrs }}}
      EncodeTxnFastPrepareRequest #ts #pwrsP (to_val ptgsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        own_map pwrsP q pwrs ∗
        ⌜encode_txnreq (FastPrepareReq ts pwrs ptgs) data⌝
    }}}.
  Proof.
    iIntros "#Hptgs".
    iIntros (Φ) "!> Hpwrs HΦ".
    wp_rec.

    (*@ func EncodeTxnFastPrepareRequest(ts uint64, pwrs tulip.KVMap, ptgs []uint64) []byte { @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_FAST_PREPARE)                   @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := util.EncodeKVMap(bs2, pwrs)                                  @*)
    (*@     data := util.EncodeInts(bs3, ptgs)                                  @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_EncodeKVMap with "[$Hbs $Hpwrs]").
    iIntros (p3 mdata) "(Hbs & Hpwrs & %Hmdata)".
    wp_apply (wp_EncodeInts__encode_txnptgs with "Hptgs Hbs").
    iIntros (dataP gdata) "[Hdata %Hgdata]".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite /= /encode_fast_prepare_req /encode_fast_prepare_req_xkind.
    list_simplifier.
    by eauto 10.
  Qed.

  Theorem wp_EncodeTxnValidateRequest
    (ts rank : u64) (pwrsP : loc) (ptgsP : Slice.t) q (pwrs : dbmap) (ptgs : txnptgs) :
    is_txnptgs_in_slice ptgsP ptgs -∗
    {{{ own_map pwrsP q pwrs }}}
      EncodeTxnValidateRequest #ts #rank #pwrsP (to_val ptgsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        own_map pwrsP q pwrs ∗
        ⌜encode_txnreq (ValidateReq ts rank pwrs ptgs) data⌝
    }}}.
  Proof.
    iIntros "#Hptgs".
    iIntros (Φ) "!> Hpwrs HΦ".
    wp_rec.

    (*@ func EncodeTxnValidateRequest(ts, rank uint64, pwrs tulip.KVMap, ptgs []uint64) []byte { @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_VALIDATE)                       @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     bs3 := marshal.WriteInt(bs2, rank)                                  @*)
    (*@     bs4 := util.EncodeKVMap(bs3, pwrs)                                  @*)
    (*@     data := util.EncodeKVMap(bs4, pwrs)                                 @*)
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
    wp_apply (wp_EncodeKVMap with "[$Hbs $Hpwrs]").
    iIntros (p4 mdata) "(Hbs & Hpwrs & %Hmdata)".
    wp_apply (wp_EncodeInts__encode_txnptgs with "Hptgs Hbs").
    iIntros (dataP gdata) "[Hdata %Hgdata]".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite /= /encode_validate_req /encode_validate_req_xkind.
    list_simplifier.
    by eauto 10.
  Qed.

  Theorem wp_EncodeTxnPrepareRequest (ts : u64) (rank : u64) :
    {{{ True }}}
      EncodeTxnPrepareRequest #ts #rank
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (PrepareReq ts rank) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnPrepareRequest(ts, rank uint64) []byte {                  @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_PREPARE)                        @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, rank)                                 @*)
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
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnUnprepareRequest (ts : u64) (rank : u64) :
    {{{ True }}}
      EncodeTxnUnprepareRequest #ts #rank
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (UnprepareReq ts rank) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnUnprepareRequest(ts, rank uint64) []byte {                @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_UNPREPARE)                      @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, rank)                                 @*)
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
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnQueryRequest (ts : u64) (rank : u64) :
    {{{ True }}}
      EncodeTxnQueryRequest #ts #rank
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (QueryReq ts rank) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnQueryRequest(ts, rank uint64) []byte {                    @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_QUERY)                          @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, rank)                                 @*)
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
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnInquireRequest (ts : u64) (rank : u64) (cid : coordid) :
    {{{ True }}}
      EncodeTxnInquireRequest #ts #rank (coordid_to_val cid)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (InquireReq ts rank cid) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnInquireRequest(ts, rank uint64) []byte {                  @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_INQUIRE)                        @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, rank)                                 @*)
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
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    iFrame.
    rewrite /encode_txnreq /encode_inquire_req /encode_inquire_req_xkind /encode_ts_rank.
    by list_simplifier.
  Qed.

  Theorem wp_EncodeTxnRefreshRequest (ts : u64) (rank : u64) :
    {{{ True }}}
      EncodeTxnRefreshRequest #ts #rank
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (RefreshReq ts rank) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnRefreshRequest(ts, rank uint64) []byte {                  @*)
    (*@     bs := make([]byte, 0, 24)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_REFRESH)                        @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := marshal.WriteInt(bs2, rank)                                 @*)
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
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

  Theorem wp_EncodeTxnCommitRequest (ts : u64) (pwrsP : loc) q (pwrs : dbmap) :
    {{{ own_map pwrsP q pwrs }}}
      EncodeTxnCommitRequest #ts (to_val pwrsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        own_map pwrsP q pwrs ∗
        ⌜encode_txnreq (CommitReq ts pwrs) data⌝
    }}}.
  Proof.
    iIntros (Φ) "Hpwrs HΦ".
    wp_rec.

    (*@ func EncodeTxnCommitRequest(ts uint64, pwrs tulip.KVMap) []byte {       @*)
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_COMMIT)                         @*)
    (*@     bs2 := marshal.WriteInt(bs1, ts)                                    @*)
    (*@     data := util.EncodeKVMap(bs2, pwrs)                                 @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_EncodeKVMap with "[$Hbs $Hpwrs]").
    iIntros (dataP mdata) "(Hdata & Hpwrs & %Hmdata)".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -app_assoc.
    iApply "HΦ".
    iFrame.
    iPureIntro.
    rewrite /= /encode_commit_req /encode_commit_req_xkind.
    by eauto.
  Qed.

  Theorem wp_EncodeTxnAbortRequest (ts : u64) :
    {{{ True }}}
      EncodeTxnAbortRequest #ts
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜encode_txnreq (AbortReq ts) data⌝
    }}}.
  Proof.
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeTxnAbortRequest(ts uint64) []byte {                          @*)
    (*@     bs := make([]byte, 0, 16)                                           @*)
    (*@     bs1 := marshal.WriteInt(bs, MSG_TXN_ABORT)                          @*)
    (*@     data := marshal.WriteInt(bs1, ts)                                   @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (p) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l.
    iApply "HΦ".
    by iFrame.
  Qed.

End encode.
