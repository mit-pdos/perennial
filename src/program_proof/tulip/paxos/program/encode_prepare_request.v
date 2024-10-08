From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section encode_prepare_request.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodePrepareRequest (term : u64) (lsnc : u64) :
    {{{ True }}}
      EncodePrepareRequest #term #lsnc
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxreq (RequestVoteReq term lsnc)⌝
    }}}.
  Proof.
    (*@ func EncodePrepareRequest(term uint64, lsnc uint64) []byte {            @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

End encode_prepare_request.
