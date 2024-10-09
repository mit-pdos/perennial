From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section encode_prepare_response.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodePrepareResponse
    (nid term terma : u64) (entsP : Slice.t) (ents : list string) :
    {{{ own_slice entsP stringT (DfracOwn 1) ents }}}
      EncodePrepareResponse #nid #term #terma (to_val entsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxresp (RequestVoteResp nid term terma ents)⌝
    }}}.
  Proof.
    iIntros (Φ) "Hents HΦ".
    wp_rec.

    (*@ func EncodePrepareResponse(nid, term, terma uint64, ents []string) []byte { @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

End encode_prepare_response.
