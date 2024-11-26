From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_string.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeValue (bsP : Slice.t) (v : dbval) (bs : list u8) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodeValue (to_val bsP) (dbval_to_val v)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_dbval v)
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func EncodeValue(bs []byte, v tulip.Value) []byte {                     @*)
    (*@     if !v.Present {                                                     @*)
    (*@         data := marshal.WriteBool(bs, false)                            @*)
    (*@         return data                                                     @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    destruct v as [s |]; last first.
    { wp_apply (wp_WriteBool with "Hbs").
      iIntros (p1) "Hp1".
      wp_pures.
      by iApply "HΦ".
    }

    (*@     bs1 := marshal.WriteBool(bs, true)                                  @*)
    (*@     data := EncodeString(bs1, v.Content)                                @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_WriteBool with "Hbs").
    iIntros (p1) "Hp1".
    wp_apply (wp_EncodeString with "Hp1").
    iIntros (p2) "Hp2".
    wp_pures.
    iApply "HΦ".
    by rewrite -app_assoc.
  Qed.

End program.
