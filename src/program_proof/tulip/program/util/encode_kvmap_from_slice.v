From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_write_entry.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeKVMapFromSlice (bsP : Slice.t) (xsP : Slice.t) (bs : list u8) (m : dbmap) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs ∗ own_dbmap_in_slice_frac xsP m }}}
      EncodeKVMapFromSlice (to_val bsP) (to_val xsP)
    {{{ (dataP : Slice.t) (mdata : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ mdata) ∗
        own_dbmap_in_slice_frac xsP m ∗
        ⌜encode_dbmap m mdata⌝
    }}}.
  Proof.
    iIntros (Φ) "[Hbs Hm] HΦ".
    wp_rec.

    (*@ func EncodeKVMapFromSlice(bs []byte, xs []tulip.WriteEntry) []byte {    @*)
    (*@     var data = marshal.WriteInt(bs, uint64(len(xs)))                    @*)
    (*@                                                                         @*)
    wp_apply wp_slice_len.
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p) "Hp".
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".

    (*@     for _, x := range(xs) {                                             @*)
    (*@         data = EncodeWriteEntry(data, x)                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    iDestruct "Hm" as (xs q) "[Hm %Hxs]".
    iDestruct (own_slice_small_sz with "Hm") as %Hlenm.
    set nW := xsP.(Slice.sz).
    set P := (λ (i : u64), ∃ (px : Slice.t),
                 let l := encode_dbmods_xlen (take (uint.nat i) xs) in
                "HdataP" ∷ dataP ↦[slice.T byteT] px ∗
                "Hdata"  ∷ own_slice px byteT (DfracOwn 1) (bs ++ u64_le nW ++ l))%I.
    wp_apply (wp_forSlice P with "[] [$Hm Hp $HdataP]"); last first; first 1 last.
    { replace (uint.nat (W64 0)) with (0%nat) by word.
      rewrite /encode_dbmods_xlen /serialize.serialize.
      by list_simplifier. }
    { clear Φ.
      iIntros (i x Φ) "!> [HP %Hloop] HΦ".
      destruct Hloop as [Hi Hx].
      iNamed "HP".
      wp_load.
      wp_apply (wp_EncodeWriteEntry with "Hdata").
      iIntros (py) "Hpy".
      wp_store.
      iApply "HΦ".
      iFrame.
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hx) encode_dbmods_xlen_snoc -app_assoc.
      by list_simplifier.
    }
    iIntros "[HP Hm]".
    iNamed "HP".
    wp_load.

    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    iPureIntro.
    split; first done.
    exists xs.
    split; last done.
    subst nW.
    rewrite -Hlenm firstn_all /encode_dbmods Hlenm.
    do 2 f_equal.
    word.
  Qed.

End program.
