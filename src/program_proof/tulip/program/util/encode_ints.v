From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeInts
    (bsP : Slice.t) (nsP : Slice.t) (bs : list u8) q (ns : list u64) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs ∗
        own_slice_small nsP uint64T q ns
    }}}
      EncodeInts (to_val bsP) (to_val nsP)
    {{{ (dataP : Slice.t), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ encode_u64s ns) ∗
        own_slice_small nsP uint64T q ns
    }}}.
  Proof.
    iIntros (Φ) "[Hbs Hns] HΦ".
    wp_rec.

    (*@ func EncodeInts(bs []byte, ns []uint64) []byte {                        @*)
    (*@     var data = marshal.WriteInt(bs, uint64(len(ns)))                    @*)
    (*@                                                                         @*)
    wp_apply wp_slice_len.
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p) "Hp".
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".

    (*@     for _, s := range(ns) {                                             @*)
    (*@         data = marshal.WriteInt(data, s)                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct (own_slice_small_sz with "Hns") as %Hlenns.
    set nW := nsP.(Slice.sz).
    set P := (λ (i : u64), ∃ (px : Slice.t),
                 let l := encode_u64s_xlen (take (uint.nat i) ns) in
                "HdataP" ∷ dataP ↦[slice.T byteT] px ∗
                "Hdata"  ∷ own_slice px byteT (DfracOwn 1) (bs ++ u64_le nW ++ l))%I.
    wp_apply (wp_forSlice P with "[] [$Hns Hp $HdataP]"); last first; first 1 last.
    { replace (uint.nat (W64 0)) with (0%nat) by word.
      rewrite /encode_u64s_xlen /serialize.serialize.
      by list_simplifier. }
    { clear Φ.
      iIntros (i s Φ) "!> [HP %Hloop] HΦ".
      destruct Hloop as [Hi Hs].
      iNamed "HP".
      wp_load.
      wp_apply (wp_WriteInt with "Hdata").
      iIntros (py) "Hpy".
      wp_store.
      iApply "HΦ".
      iFrame.
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hs) encode_u64s_xlen_snoc.
      by list_simplifier.
    }
    iIntros "[HP Hns]".
    iNamed "HP".
    wp_load.

    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    subst nW.
    rewrite /encode_u64s Hlenns w64_to_nat_id.
    by rewrite -Hlenns firstn_all.
  Qed.

  Theorem wp_EncodeInts__encode_txnptgs
    (bsP : Slice.t) (nsP : Slice.t) (ptgs : txnptgs) (bs : list u8) :
    is_txnptgs_in_slice nsP ptgs -∗
    {{{ own_slice bsP byteT (DfracOwn 1) bs }}}
      EncodeInts (to_val bsP) (to_val nsP)
    {{{ (dataP : Slice.t) (gdata : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ gdata) ∗
        ⌜encode_txnptgs ptgs gdata⌝
    }}}.
  Proof.
    iIntros "#Hptgs".
    iIntros (Φ) "!> Hbs HΦ".
    iDestruct "Hptgs" as (ns) "[Hns %Hptgs]".
    wp_apply (wp_EncodeInts with "[$Hbs $Hns]").
    iIntros (p) "[Hbs _]".
    iApply "HΦ".
    iFrame "∗ %".
    iPureIntro.
    destruct Hptgs as [Hptgs Hnd].
    by exists ns.
  Qed.

End program.
