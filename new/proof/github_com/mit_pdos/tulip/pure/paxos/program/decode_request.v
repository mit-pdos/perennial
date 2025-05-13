From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip Require Import encode.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_strings.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Definition pxreq_to_val (req : pxreq) (entsP : Slice.t) : val :=
  match req with
  | RequestVoteReq term lsnlc =>
      struct.mk_f PaxosRequest [
          ("Kind", #(U64 0)); ("Term", #term); ("CommittedLSN", #lsnlc)
        ]
  | AppendEntriesReq term lsnlc lsne ents =>
      struct.mk_f PaxosRequest [
          ("Kind", #(U64 1)); ("Term", #term); ("CommittedLSN", #lsnlc);
          ("EntriesLSN", #lsne); ("Entries", to_val entsP)
        ]
  end.

Section decode_request.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodePrepareRequest (bsP : Slice.t) term lsnlc :
    let bs := encode_request_vote_req_xkind term lsnlc in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodePrepareRequest (to_val bsP)
    {{{ RET (pxreq_to_val (RequestVoteReq term lsnlc) Slice.nil); True }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodePrepareRequest(bs []byte) PaxosRequest {                     @*)
    (*@     term, bs1 := marshal.ReadInt(bs)                                    @*)
    (*@     lsnc, _ := marshal.ReadInt(bs1)                                     @*)
    (*@                                                                         @*)
    (*@     return PaxosRequest{                                                @*)
    (*@         Kind : MSG_PREPARE,                                             @*)
    (*@         Term : term,                                                    @*)
    (*@         CommittedLSN : lsnc,                                            @*)
    (*@     }                                                                   @*)
    (*@ }                                                                       @*)
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_ReadInt [] with "[Hbs]").
    { by list_simplifier. }
    iIntros (p2) "Hbs".
    wp_pures.
    by iApply "HΦ".
  Qed.

  Theorem wp_DecodeAcceptRequest (bsP : Slice.t) term lsnc lsne ents :
    let bs := encode_append_entries_req_xkind term lsnc lsne ents in
    {{{ own_slice_small bsP byteT (DfracOwn 1) bs }}}
      DecodeAcceptRequest (to_val bsP)
    {{{ (entsP : Slice.t), RET (pxreq_to_val (AppendEntriesReq term lsnc lsne ents) entsP); 
        own_slice entsP stringT (DfracOwn 1) ents
    }}}.
  Proof.
    iIntros (Henc Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeAcceptRequest(bs []byte) PaxosRequest {                      @*)
    (*@     term, bs1 := marshal.ReadInt(bs)                                    @*)
    (*@     lsnc, bs2 := marshal.ReadInt(bs1)                                   @*)
    (*@     lsne, bs3 := marshal.ReadInt(bs2)                                   @*)
    (*@     ents, _ := util.DecodeStrings(bs3)                                  @*)
    (*@                                                                         @*)
    (*@     return PaxosRequest{                                                @*)
    (*@         Kind         : MSG_ACCEPT,                                      @*)
    (*@         Term         : term,                                            @*)
    (*@         CommittedLSN : lsnc,                                            @*)
    (*@         EntriesLSN   : lsne,                                            @*)
    (*@         Entries      : ents,                                            @*)
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

  Theorem wp_DecodeRequest (dataP : Slice.t) (req : pxreq) :
    let data := encode_pxreq req in
    {{{ own_slice_small dataP byteT (DfracOwn 1) data }}}
      DecodeRequest (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxreq_to_val req entsP);
        match req with
        | RequestVoteReq _ _ => True
        | AppendEntriesReq _ _ _ ents => own_slice entsP stringT (DfracOwn 1) ents
        end
    }}}.
  Proof.
    iIntros (bs Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeRequest(bs []byte) PaxosRequest {                            @*)
    (*@     kind, data := marshal.ReadInt(bs)                                   @*)
    (*@                                                                         @*)
    (*@     if kind == MSG_PREPARE {                                            @*)
    (*@         req := DecodePrepareRequest(data)                               @*)
    (*@         return req                                                      @*)
    (*@     }                                                                   @*)
    (*@     if kind == MSG_ACCEPT {                                             @*)
    (*@         req := DecodeAcceptRequest(data)                                @*)
    (*@         return req                                                      @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct req; wp_pures.
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodePrepareRequest with "Hbs").
      wp_pures.
      (* TODO: figure why need this application here while not required in [gcoord/decode.v]. *)
      by iApply ("HΦ" $! Slice.nil).
    }
    { wp_apply (wp_ReadInt with "Hbs").
      iIntros (p) "Hbs".
      wp_pures.
      wp_apply (wp_DecodeAcceptRequest with "Hbs").
      iIntros (entsP) "Hents".
      wp_pures.
      by iApply "HΦ".
    }

    (*@     return PaxosRequest{}                                               @*)
    (*@ }                                                                       @*)
  Qed.

End decode_request.
