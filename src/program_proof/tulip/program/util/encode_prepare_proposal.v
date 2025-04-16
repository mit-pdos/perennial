From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodePrepareProposal (bsP : Slice.t) (pp : ppsl) (bs : list u8) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodePrepareProposal (to_val bsP) (ppsl_to_val pp)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_ppsl pp)
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func EncodePrepareProposal(bs []byte, pp tulip.PrepareProposal) []byte { @*)
    (*@     bs1 := marshal.WriteInt(bs, pp.Rank)                                @*)
    (*@     data := marshal.WriteBool(bs1, pp.Prepared)                         @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    rewrite -app_assoc.
    by iApply "HΦ".
  Qed.

End program.
