From New.proof.github_com.mit_pdos.tulip.pure Require Import prelude.
From New.proof.github_com.mit_pdos.tulip Require Import program_prelude.
From New.proof Require Import grove_prelude.
From New.proof.github_com.mit_pdos.tulip.util_proof Require Import init.

Section program.
  Context `{!heapGS Σ} `{!goGlobalsGS Σ}.

  Theorem wp_DecodeInts (bsP : slice.t) (ns : list u64) (bstail : list u8) :
    {{{ is_pkg_init util ∗ own_slice bsP (DfracOwn 1) (encode_u64s ns ++ bstail) }}}
      util @ "DecodeInts" #bsP
    {{{ (nsP : slice.t) (dataP : slice.t), RET (to_val nsP, to_val dataP);
        own_slice nsP (DfracOwn 1) ns ∗
        own_slice dataP (DfracOwn 1) bstail
    }}}.
  Proof.
    wp_start as "Hbs".
    wp_auto.
    iDestruct (own_slice_len with "Hbs") as %Hlenbs.
    assert (Hlenns : length ns < 2 ^ 64).
    { rewrite length_app in Hlenbs.
      assert (Hlen : (length (encode_u64s ns) ≤ uint.nat bsP.(slice.len_f))%nat) by lia.
      apply encode_u64s_length_inv in Hlen.
      word.
    }

    (*@ func DecodeInts(bs []byte) ([]uint64, []byte) {                         @*)
    (*@     n, bs1 := marshal.ReadInt(bs)                                       @*)
    (*@                                                                         @*)
    rewrite /encode_u64s -app_assoc.
    wp_apply (wp_ReadInt with "[$Hbs]").
    iIntros (p) "Hp".
    wp_auto.

    (*@     var data = bs1                                                      @*)
    (*@     var ents = make([]uint64, 0, n)                                     @*)
    (*@                                                                         @*)
    wp_apply (wp_slice_make3 (V:=w64)).
    { word. }
    iIntros (entsbaseP) "(Hents & Hents_cap & %Hents_cap)". wp_auto.

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < n {                                                         @*)
    (*@         s, bsloop := marshal.ReadInt(data)                              @*)
    (*@         ents = append(ents, s)                                          @*)
    (*@         data = bsloop                                                   @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iPersist "n".
    set P := (∃ (i : u64) (p1 p2 : slice.t),
                 let remaining := encode_u64s_xlen (drop (uint.nat i) ns) ++ bstail in
                 "HdataP"    ∷ data_ptr ↦ p1 ∗
                 "HentsP"    ∷ ents_ptr ↦ p2 ∗
                 "HiP"       ∷ i_ptr ↦ i ∗
                 "Hns"       ∷ own_slice p1 (DfracOwn 1) remaining ∗
                 "Hents"     ∷ own_slice p2 (DfracOwn 1) (take (uint.nat i) ns) ∗
                 "Hents_cap" ∷ own_slice_cap w64 p2 ∗
                 "%Hbound"   ∷ ⌜uint.Z i ≤ Z.of_nat (length ns)⌝)%I.
    iAssert P with "[-HΦ]" as "IH".
    {
      iFrame.
      word.
    }
    wp_for "IH".
    case_bool_decide as Hi; try wp_auto.
    {
      assert (is_Some (ns !! uint.nat i)) as [s Hs].
      { apply lookup_lt_is_Some_2. word. }
      rewrite (drop_S _ _ _ Hs) encode_u64s_xlen_cons -app_assoc.
      wp_apply (wp_ReadInt with "[$Hns]").
      iIntros (bsloopP) "Hbsloop".
      wp_auto.
      wp_apply (wp_slice_literal).
      iIntros (ents_tmp) "ents_tmp". wp_auto.
      wp_apply (wp_slice_append with "[$Hents $Hents_cap $ents_tmp]").
      iIntros (entsP') "(Hents & Hents_cap & _)".
      wp_auto.
      wp_for_post.
      iFrame "∗ %".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hs).
      iFrame.
      word.
    }

    assert (uint.Z i = Z.of_nat (length ns)) by word.
    iApply "HΦ".
    rewrite -> take_ge by len.
    rewrite -> drop_ge by len.
    iFrame.
  Qed.

  Theorem wp_DecodeInts__encode_txnptgs
    (bsP : slice.t) (ptgs : txnptgs) (gdata : list u8) (bstail : list u8) :
    encode_txnptgs ptgs gdata ->
    {{{ is_pkg_init util ∗ own_slice bsP (DfracOwn 1) (gdata ++ bstail) }}}
      util@"DecodeInts" #bsP
    {{{ (nsP : slice.t) (dataP : slice.t), RET (#nsP, #dataP);
        is_txnptgs_in_slice nsP ptgs ∗
        own_slice dataP (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Henc). wp_start_folded as "Hbs".
    destruct Henc as (ns & -> & Hptgs).
    iApply wp_fupd.
    wp_apply (wp_DecodeInts with "[$Hbs]").
    iIntros (nsP dataP) "[Hns Hdata]".
    iPersist "Hns".
    iModIntro.
    iApply "HΦ".
    by iFrame "∗ #".
  Qed.

End program.
