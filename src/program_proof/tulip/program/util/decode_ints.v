From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ}.

  Theorem wp_DecodeInts (bsP : Slice.t) (ns : list u64) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_u64s ns ++ bstail) }}}
      DecodeInts (to_val bsP)
    {{{ (nsP : Slice.t) (dataP : Slice.t), RET (to_val nsP, to_val dataP);
        own_slice nsP uint64T (DfracOwn 1) ns ∗
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.
    iDestruct (own_slice_small_sz with "Hbs") as %Hlenbs.
    assert (Hlenns : length ns < 2 ^ 64).
    { rewrite length_app in Hlenbs.
      assert (Hlen : (length (encode_u64s ns) ≤ uint.nat bsP.(Slice.sz))%nat) by lia.
      apply encode_u64s_length_inv in Hlen.
      word.
    }

    (*@ func DecodeInts(bs []byte) ([]uint64, []byte) {                         @*)
    (*@     n, bs1 := marshal.ReadInt(bs)                                       @*)
    (*@                                                                         @*)
    rewrite /encode_u64s -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p) "Hp".

    (*@     var data = bs1                                                      @*)
    (*@     var ents = make([]uint64, 0, n)                                     @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (entsbaseP) "Hents".
    wp_apply wp_ref_to; first done.
    iIntros (entsP) "HentsP".

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < n {                                                         @*)
    (*@         s, bsloop := marshal.ReadInt(data)                              @*)
    (*@         ents = append(ents, s)                                          @*)
    (*@         data = bsloop                                                   @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    wp_pures.
    set P := (λ cont : bool, ∃ (i : u64) (p1 p2 : Slice.t),
                 let remaining := encode_u64s_xlen (drop (uint.nat i) ns) ++ bstail in
                 "HdataP"  ∷ dataP ↦[slice.T byteT] p1 ∗
                 "HentsP"  ∷ entsP ↦[slice.T uint64T] p2 ∗
                 "HiP"     ∷ iP ↦[uint64T] #i ∗
                 "Hns"     ∷ own_slice_small p1 byteT (DfracOwn 1) remaining ∗
                 "Hents"   ∷ own_slice p2 uint64T (DfracOwn 1) (take (uint.nat i) ns) ∗
                 "%Hbound" ∷ ⌜cont || bool_decide (length ns ≤ uint.nat i)%nat⌝)%I.
    wp_apply (wp_forBreak_cond P with "[] [-HΦ]"); last first; first 1 last.
    { by iFrame. }
    { clear Φ.
      iIntros (Φ) "!> HP HΦ".
      iNamed "HP".
      wp_load.
      wp_pures.
      set b := bool_decide _.
      destruct b eqn:Hb; wp_pures; last first.
      { iApply "HΦ".
        iFrame.
        iPureIntro.
        subst b.
        case_bool_decide as Hi; first done.
        apply bool_decide_pack.
        word.
      }
      wp_load.
      subst b. apply bool_decide_eq_true_1 in Hb.
      assert (is_Some (ns !! uint.nat i)) as [s Hs].
      { apply lookup_lt_is_Some_2. word. }
      rewrite (drop_S _ _ _ Hs) encode_u64s_xlen_cons -app_assoc.
      wp_apply (wp_ReadInt with "Hns").
      iIntros (bsloopP) "Hbsloop".
      wp_load.
      wp_apply (wp_SliceAppend with "Hents").
      iIntros (entsP') "Hents".
      do 2 wp_store. wp_load. wp_store.
      iApply "HΦ".
      iFrame "∗ %".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hs).
      by iFrame.
    }
    iNamed 1.
    case_bool_decide as Hi; last done.
    do 2 wp_load.
    wp_pures.

    (*@     return ents, data                                                   @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    rewrite take_ge; last apply Hi.
    rewrite drop_ge; last apply Hi.
    by iFrame.
  Qed.

  Theorem wp_DecodeInts__encode_txnptgs
    (bsP : Slice.t) (ptgs : txnptgs) (gdata : list u8) (bstail : list u8) :
    encode_txnptgs ptgs gdata ->
    {{{ own_slice_small bsP byteT (DfracOwn 1) (gdata ++ bstail) }}}
      DecodeInts (to_val bsP)
    {{{ (nsP : Slice.t) (dataP : Slice.t), RET (to_val nsP, to_val dataP);
        is_txnptgs_in_slice nsP ptgs ∗
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Henc Φ) "Hbs HΦ".
    destruct Henc as (ns & -> & Hptgs).
    iApply wp_fupd.
    wp_apply (wp_DecodeInts with "Hbs").
    iIntros (nsP dataP) "[Hns Hdata]".
    iDestruct (own_slice_to_small with "Hns") as "Hns".
    iMod (own_slice_small_persist with "Hns") as "#Hns".
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
