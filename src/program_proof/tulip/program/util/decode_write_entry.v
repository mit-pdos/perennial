From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_string decode_value.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeWriteEntry (bsP : Slice.t) (x : dbmod) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_dbmod x ++ bstail) }}}
      DecodeWriteEntry (to_val bsP)
    {{{ (dataP : Slice.t), RET (dbmod_to_val x, (to_val dataP));
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeWriteEntry(bs []byte) (tulip.WriteEntry, []byte) {           @*)
    (*@     k, bs1 := DecodeString(bs)                                          @*)
    (*@     v, data := DecodeValue(bs1)                                         @*)
    (*@     x := tulip.WriteEntry{                                              @*)
    (*@         Key   : k,                                                      @*)
    (*@         Value : v,                                                      @*)
    (*@     }                                                                   @*)
    (*@     return x, data                                                      @*)
    (*@ }                                                                       @*)
    rewrite /encode_dbmod -app_assoc.
    wp_apply (wp_DecodeString with "Hbs").
    iIntros (bs1P) "Hbs".
    wp_apply (wp_DecodeValue with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
