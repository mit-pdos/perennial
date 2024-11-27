From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_value.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeVersion (bsP : Slice.t) (x : dbpver) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_dbpver x ++ bstail) }}}
      DecodeVersion (to_val bsP)
    {{{ (dataP : Slice.t), RET (dbpver_to_val x, (to_val dataP));
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeVersion(bs []byte) (tulip.Version, []byte) {                 @*)
    (*@     ts, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     v, data := DecodeValue(bs1)                                         @*)
    (*@     x := tulip.Version{                                                 @*)
    (*@         Timestamp : ts,                                                 @*)
    (*@         Value     : v,                                                  @*)
    (*@     }                                                                   @*)
    (*@     return x, data                                                      @*)
    (*@ }                                                                       @*)
    rewrite /encode_dbpver -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (bs1P) "Hbs".
    wp_apply (wp_DecodeValue with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
