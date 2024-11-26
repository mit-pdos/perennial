From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_string.
From Perennial.program_proof Require Import marshal_stateless_proof.

Opaque encode_string.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeValue (bsP : Slice.t) (v : dbval) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_dbval v ++ bstail) }}}
      DecodeValue (to_val bsP)
    {{{ (dataP : Slice.t), RET (dbval_to_val v, (to_val dataP));
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeValue(bs []byte) (tulip.Value, []byte) {                     @*)
    (*@     b, bs1 := marshal.ReadBool(bs)                                      @*)
    (*@                                                                         @*)

    (*@     if !b {                                                             @*)
    (*@         v := tulip.Value{                                               @*)
    (*@             Present : false,                                            @*)
    (*@             Content : "",                                               @*)
    (*@         }                                                               @*)
    (*@         return v, bs1                                                   @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct v as [s |]; wp_pures; last first.
    { wp_apply (wp_ReadBool with "Hbs").
      iIntros (b bs1) "[%Hb Hbs]".
      replace (uint.Z (W8 0)) with 0 in Hb; last word.
      simpl in Hb. subst b.
      wp_pures.
      by iApply "HΦ".
    }

    (*@     s, data := DecodeString(bs1)                                        @*)
    (*@     v := tulip.Value{                                                   @*)
    (*@         Present : true,                                                 @*)
    (*@         Content : s,                                                    @*)
    (*@     }                                                                   @*)
    (*@     return v, data                                                      @*)
    (*@ }                                                                       @*)
    simpl.
    wp_apply (wp_ReadBool with "Hbs").
    iIntros (b bs1) "[%Hb Hbs]".
    replace (uint.Z (W8 1)) with 1 in Hb; last word.
    simpl in Hb. subst b.
    wp_apply (wp_DecodeString with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
