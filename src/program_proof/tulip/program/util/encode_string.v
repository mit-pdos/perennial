From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeString (bsP : Slice.t) (s : byte_string) (bs : list u8) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodeString (to_val bsP) #(LitString s)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_string s)
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.

    (*@ func EncodeString(bs []byte, str string) []byte {                       @*)
    (*@     bs1 := marshal.WriteInt(bs, uint64(len(str)))                       @*)
    (*@     data := marshal.WriteBytes(bs1, []byte(str))                        @*)
    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p1) "Hp1".
    wp_apply wp_StringToBytes.
    iIntros (p2) "Hp2".
    iDestruct (own_slice_to_small with "Hp2") as "Hp2".
    wp_apply (wp_WriteBytes with "[$Hp1 $Hp2]").
    iIntros (p3) "[Hp3 Hp2]".
    wp_pures.
    iApply "HΦ".
    iFrame.
    by rewrite -app_assoc /encode_string.
  Qed.

End program.
