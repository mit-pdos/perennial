From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip Require Import encode.
From Perennial.program_proof.tulip.program.util Require Import encode_strings.
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
    iIntros (Φ) "_ HΦ".
    wp_rec.

    (*@ func EncodeAcceptResponse(nid, term, lsn uint64) []byte {               @*)
    (*@     bs := make([]byte, 0, 32)                                           @*)
    (*@                                                                         @*)
    (*@     bs1  := marshal.WriteInt(bs, MSG_ACCEPT)                            @*)
    (*@     bs2  := marshal.WriteInt(bs1, nid)                                  @*)
    (*@     bs3  := marshal.WriteInt(bs2, term)                                 @*)
    (*@     data := marshal.WriteInt(bs3, lsn)                                  @*)
    (*@                                                                         @*)
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

End encode_accept_request.
