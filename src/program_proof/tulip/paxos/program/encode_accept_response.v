From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section encode_accept_request.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeAcceptResponse (nid : u64) (term : u64) (lsn : u64) :
    {{{ True }}}
      EncodeAcceptResponse #nid #term #lsn
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxresp (AppendEntriesResp nid term lsn)⌝
    }}}.
  Proof.
    (*@ func EncodeAcceptResponse(nid, term uint64, lsn uint64) []byte {        @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

End encode_accept_request.
