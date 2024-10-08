From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Definition pxresp_to_val (resp : pxresp) (entsP : Slice.t) : val :=
  match resp with
  | RequestVoteResp nid term terme ents =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 0)); ("NodeID", #nid); ("Term", #term);
          ("TermEntries", #terme); ("Entries", to_val entsP)
        ]
  | AppendEntriesResp nid term lsneq =>
      struct.mk_f PaxosResponse [
          ("Kind", #(U64 1)); ("NodeID", #nid); ("Term", #term);
          ("MatchedLSN", #lsneq)
        ]
  end.

Section decode_response.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeResponse (dataP : Slice.t) (data : list u8) (resp : pxresp) :
    data = encode_pxresp resp ->
    {{{ True }}}
      DecodeResponse (to_val dataP)
    {{{ (entsP : Slice.t), RET (pxresp_to_val resp entsP);
        match resp with
        | RequestVoteResp nid term terme ents => own_slice entsP stringT (DfracOwn 1) ents
        | AppendEntriesResp _ _ _ => True
        end
    }}}.
  Proof.
    (*@ func DecodeResponse(data []byte) PaxosResponse {                        @*)
    (*@     return PaxosResponse{}                                              @*)
    (*@ }                                                                       @*)
  Admitted.

End decode_response.
