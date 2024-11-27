From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_value.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeVersion (bsP : Slice.t) (x : dbpver) (bs : list u8) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodeVersion (to_val bsP) (dbpver_to_val x)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_dbpver x)
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func EncodeVersion(bs []byte, x tulip.Version) []byte {                 @*)
    (*@     bs1 := marshal.WriteInt(bs, x.Timestamp)                            @*)
    (*@     data := EncodeValue(bs1, x.Value)                                   @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_EncodeValue with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    rewrite -app_assoc.
    by iApply "HΦ".
  Qed.

End program.
