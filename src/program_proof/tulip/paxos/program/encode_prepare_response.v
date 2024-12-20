From Perennial.program_proof Require Import marshal_stateless_proof.
From Perennial.program_proof.tulip.paxos Require Import prelude.
From Perennial.program_proof.tulip Require Import encode.
From Perennial.program_proof.tulip.program.util Require Import encode_strings.
From Goose.github_com.mit_pdos.tulip Require Import paxos.

Section encode_prepare_response.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodePrepareResponse
    (nid term terma : u64) (entsP : Slice.t) (ents : list byte_string) :
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
    (*@     bs := make([]byte, 0, 64)                                           @*)
    (*@                                                                         @*)
    (*@     bs1  := marshal.WriteInt(bs, MSG_PREPARE)                           @*)
    (*@     bs2  := marshal.WriteInt(bs1, nid)                                  @*)
    (*@     bs3  := marshal.WriteInt(bs2, term)                                 @*)
    (*@     bs4  := marshal.WriteInt(bs3, terma)                                @*)
    (*@     data := util.EncodeStrings(bs4, ents)                               @*)
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
    iDestruct (own_slice_to_small with "Hents") as "Hents".
    wp_apply (wp_EncodeStrings with "[$Hbs $Hents]").
    iIntros (dataP) "[Hdata Hents]".
    wp_pures.
    rewrite uint_nat_W64_0 replicate_0 app_nil_l -!app_assoc.
    iApply "HΦ".
    by iFrame.
  Qed.

End encode_prepare_response.
