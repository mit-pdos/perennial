From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip Require Import encode.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_strings.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Definition pxresp_to_val (resp : pxresp) (entsP : Slice.t) : val :=
  match resp with
  | RequestVoteResp nid term terme ents =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 0)); ("NodeID", #nid); ("Term", #term);
          ("EntriesTerm", #terme); ("Entries", to_val entsP)
        ]
  | AppendEntriesResp nid term lsneq =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 1)); ("NodeID", #nid); ("Term", #term);
          ("MatchedLSN", #lsneq)
        ]
  end.

Section decode_response.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodePrepareResponse (bsP : Slice.t) nid term terme ents :
    let bs := encode_request_vote_resp_xkind nid term terme ents in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodePrepareResponse (to_val bsP)
    {{{ (entsP : Slice.t), RET (pxresp_to_val (RequestVoteResp nid term terme ents) entsP);
        own_slice entsP stringT (DfracOwn 1) ents
    }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodePrepareResponse(bs []byte) PaxosResponse {                   @*)
    (*@     nid, bs1   := marshal.ReadInt(bs)                                   @*)
    (*@     term, bs2  := marshal.ReadInt(bs1)                                  @*)
    (*@     terma, bs3 := marshal.ReadInt(bs2)                                  @*)
    (*@     ents, _    := util.DecodeStrings(bs3)                               @*)
    (*@                                                                         @*)
    (*@     return PaxosResponse{                                               @*)
    (*@         Kind        : MSG_PREPARE,                                      @*)
    (*@         NodeID      : nid,                                              @*)
    (*@         Term        : term,                                             @*)
    (*@         EntriesTerm : terma,                                            @*)
    (*@         Entries     : ents,                                             @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p3) "Hbs".
    rewrite -(app_nil_r (encode_strings ents)).
    wp_apply (wp_DecodeStrings with "Hbs").
    iIntros (entsP dataP) "[Hents Hdata]".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeAcceptResponse (bsP : Slice.t) nid term lsneq :
    let bs := encode_append_entries_resp_xkind nid term lsneq in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeAcceptResponse (to_val bsP)
    {{{ RET (pxresp_to_val (AppendEntriesResp nid term lsneq) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeAcceptResponse(bs []byte) PaxosResponse {                    @*)
    (*@     nid, bs1  := marshal.ReadInt(bs)                                    @*)
    (*@     term, bs2 := marshal.ReadInt(bs1)                                   @*)
    (*@     lsn, _    := marshal.ReadInt(bs2)                                   @*)
    (*@                                                                         @*)
    (*@     return PaxosResponse{                                               @*)
    (*@         Kind       : MSG_ACCEPT,                                        @*)
    (*@         NodeID     : nid,                                               @*)
    (*@         Term       : term,                                              @*)
    (*@         MatchedLSN : lsn,                                               @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p2) "Hbs".
    wp_apply (wp_ReadInt [] with "[Hbs]").
    { by list_simplifier. }
    iIntros (p3) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeResponse (dataP : Slice.t) (resp : pxresp) :
    let data := encode_pxresp resp in
    {{{ own_slice_small dataP byteT (DfracOwn 1) data }}}
      DecodeResponse (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxresp_to_val resp entsP);
        match resp with
        | RequestVoteResp nid term terme ents => own_slice entsP stringT (DfracOwn 1) ents
        | AppendEntriesResp _ _ _ => True
        end
    }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeResponse(bs []byte) PaxosResponse {                          @*)
    (*@     kind, data := marshal.ReadInt(bs)                                   @*)
    (*@                                                                         @*)
    (*@     if kind == MSG_PREPARE {                                            @*)
    (*@         resp := DecodePrepareResponse(data)                             @*)
    (*@         return resp                                                     @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_ACCEPT {                                             @*)
    (*@         resp := DecodeAcceptResponse(data)                              @*)
    (*@         return resp                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    (*@     return PaxosResponse{}                                              @*)
    (*@ }                                                                       @*)
    destruct resp; wp_pures.
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodePrepareResponse with "Hbs").
      iIntros (entsP) "Hents".
      wp_pures.
      by iApply "HΦ".
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeAcceptResponse with "Hbs").
      wp_pures.
      by iApply ("HΦ" $! Slice.nil).
    }
  Qed.

End decode_response.
