From Perennial.program_proof.tulip.paxos Require Import prelude.
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

  Theorem wp_DecodeRequest (dataP : Slice.t) (data : list u8) (req : pxreq) :
    data = encode_pxreq req ->
    {{{ own_slice dataP byteT (DfracOwn 1) data }}}
      DecodeRequest (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxreq_to_val req entsP);
        match req with
        | RequestVoteReq _ _ => True
        | AppendEntriesReq _ _ _ ents => own_slice entsP stringT (DfracOwn 1) ents
        end
    }}}.
  Proof.
    iIntros (Hdataenc Φ) "Hdata HΦ".
    wp_rec.

    (*@ func DecodeRequest(data []byte) PaxosRequest {                          @*)
    (*@     return PaxosRequest{}                                               @*)
    (*@ }                                                                       @*)
  Admitted.

End decode_request.
