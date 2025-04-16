From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodePrepareProposal (bsP : Slice.t) (pp : ppsl) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_ppsl pp ++ bstail) }}}
      DecodePrepareProposal (to_val bsP)
    {{{ (dataP : Slice.t), RET (ppsl_to_val pp, (to_val dataP));
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodePrepareProposal(bs []byte) (tulip.PrepareProposal, []byte) { @*)
    (*@     rank, bs1 := marshal.ReadInt(bs)                                    @*)
    (*@     prepared, data := marshal.ReadBool(bs1)                             @*)
    (*@     pp := tulip.PrepareProposal{                                        @*)
    (*@         Rank     : rank,                                                @*)
    (*@         Prepared : prepared,                                            @*)
    (*@     }                                                                   @*)
    (*@     return pp, data                                                     @*)
    (*@ }                                                                       @*)
    rewrite /encode_ppsl -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (bs1P) "Hbs".
    wp_apply (wp_ReadBool with "Hbs").
    iIntros (b dataP) "[%Hb Hdata]".
    wp_pures.
    rewrite /ppsl_to_val.
    by case_bool_decide; subst b; destruct pp.2; try word; iApply "HΦ".
  Qed.

End program.
