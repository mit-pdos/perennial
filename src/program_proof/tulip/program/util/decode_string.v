From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeString (bsP : Slice.t) (s : byte_string) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_string s ++ bstail) }}}
      DecodeString (to_val bsP)
    {{{ (dataP : Slice.t), RET (#(LitString s), (to_val dataP));
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func DecodeString(bs []byte) (string, []byte) {                         @*)
    (*@     sz, bs1 := marshal.ReadInt(bs)                                      @*)
    (*@     bsr, data := marshal.ReadBytes(bs1, sz)                             @*)
    (*@     return string(bsr), data                                            @*)
    (*@ }                                                                       @*)
    rewrite /encode_string -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p1) "Hp1".
    wp_pures.
    iDestruct (own_slice_small_sz with "Hp1") as %Hsz.
    wp_apply (wp_ReadBytes with "Hp1").
    { rewrite uint_nat_W64_of_nat; first done.
      rewrite length_app in Hsz. word.
    }
    iIntros (p2 p3) "[Hp2 Hp3]".
    wp_apply (wp_StringFromBytes with "Hp2").
    iIntros "Hp2".
    wp_pures.
    by iApply "HΦ".
  Qed.

End program.
