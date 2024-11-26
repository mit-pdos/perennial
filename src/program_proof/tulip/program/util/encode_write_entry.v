From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_string encode_value.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeWriteEntry (bsP : Slice.t) (x : dbmod) (bs : list u8) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodeWriteEntry (to_val bsP) (dbmod_to_val x)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_dbmod x)
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func EncodeWriteEntry(bs []byte, x tulip.WriteEntry) []byte {           @*)
    (*@     bs1 := EncodeString(bs, x.Key)                                      @*)
    (*@     data := EncodeValue(bs1, x.Value)                                   @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_EncodeString with "Hbs").
    iIntros (p1) "Hbs".
    wp_apply (wp_EncodeValue with "Hbs").
    iIntros (dataP) "Hdata".
    wp_pures.
    rewrite -app_assoc.
    by iApply "HΦ".
  Qed.

End program.
