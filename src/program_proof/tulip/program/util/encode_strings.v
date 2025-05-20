From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_string.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ}.

  Theorem wp_EncodeStrings
    (bsP : Slice.t) (strsP : Slice.t) (bs : list u8) (strs : list byte_string) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs ∗
        own_slice_small strsP stringT (DfracOwn 1) strs
    }}}
      EncodeStrings (to_val bsP) (to_val strsP)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_strings strs) ∗
        own_slice_small strsP stringT (DfracOwn 1) strs
    }}}.
  Proof.
    iIntros (Φ) "[Hbs Hstrs] HΦ".
    wp_rec.

    (*@ func EncodeStrings(bs []byte, strs []string) []byte {                   @*)
    (*@     var data = marshal.WriteInt(bs, uint64(len(strs)))                  @*)
    (*@                                                                         @*)
    wp_apply wp_slice_len.
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p) "Hp".
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".

    (*@     for _, s := range(strs) {                                           @*)
    (*@         data = EncodeString(data, s)                                    @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (own_slice_small_sz with "Hstrs") as %Hlenstrs.
    set nW := strsP.(Slice.sz).
    set P := (λ (i : u64), ∃ (px : Slice.t),
                 let l := encode_strings_xlen (take (uint.nat i) strs) in
                "HdataP" ∷ dataP ↦[slice.T byteT] px ∗
                "Hdata"  ∷ own_slice px byteT (DfracOwn 1) (bs ++ u64_le nW ++ l))%I.
    wp_apply (wp_forSlice P with "[] [$Hstrs Hp $HdataP]"); last first; first 1 last.
    { replace (uint.nat (W64 0)) with (0%nat) by word.
      rewrite /encode_strings_xlen /serialize.serialize.
      by list_simplifier. }
    { clear Φ.
      iIntros (i s Φ) "!> [HP %Hloop] HΦ".
      destruct Hloop as [Hi Hs].
      iNamed "HP".
      wp_load.
      wp_apply (wp_EncodeString with "Hdata").
      iIntros (py) "Hpy".
      wp_store.
      iApply "HΦ".
      iFrame.
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hs) encode_strings_xlen_snoc.
      by list_simplifier.
    }
    iIntros "[HP Hstrs]".
    iNamed "HP".
    wp_load.

    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    subst nW.
    rewrite /encode_strings Hlenstrs w64_to_nat_id.
    by rewrite -Hlenstrs firstn_all.
  Qed.

End program.
