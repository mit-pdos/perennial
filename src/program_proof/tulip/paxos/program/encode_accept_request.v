From Perennial.program_proof.tulip.paxos Require Import prelude.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section encode_accept_request.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeAcceptRequest
    (term lsnc lsne : u64) (entsP : Slice.t) (ents : list string) :
    {{{ own_slice entsP stringT (DfracOwn 1) ents }}}
      EncodeAcceptRequest #term #lsnc #lsne (to_val entsP)
    {{{ (dataP : Slice.t) (data : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) data ∗
        ⌜data = encode_pxreq (AppendEntriesReq term lsnc lsne ents)⌝
    }}}.
  Proof.
    (*@ func EncodeAcceptRequest(term uint64, lsnc, lsne uint64, ents []string) []byte { @*)
    (*@     return nil                                                          @*)
    (*@ }                                                                       @*)
  Admitted.

End encode_accept_request.
