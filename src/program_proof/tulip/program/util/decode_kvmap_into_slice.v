From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_write_entry.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeKVMapIntoSlice
    (bsP : Slice.t) (m : dbmap) (mdata : list u8) (bstail : list u8) :
    encode_dbmap m mdata ->
    {{{ own_slice_small bsP byteT (DfracOwn 1) (mdata ++ bstail) }}}
      DecodeKVMapIntoSlice (to_val bsP)
    {{{ (entsP : Slice.t) (dataP : Slice.t), RET (to_val entsP, to_val dataP);
        own_dbmap_in_slice entsP m ∗
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Hmdata Φ) "Hbs HΦ".
    wp_rec.
    destruct Hmdata as (xs & Hmdata & Hxs).
    iDestruct (own_slice_small_sz with "Hbs") as %Hlenbs.
    assert (Hlenxs : length xs < 2 ^ 64).
    { rewrite length_app in Hlenbs.
      assert (Hlen : (length mdata ≤ uint.nat bsP.(Slice.sz))%nat) by lia.
      rewrite Hmdata in Hlen.
      apply encode_dbmods_length_inv in Hlen.
      word.
    }

    (*@ func DecodeKVMapIntoSlice(bs []byte) ([]tulip.WriteEntry, []byte) {     @*)
    (*@     n, bs1 := marshal.ReadInt(bs)                                       @*)
    (*@                                                                         @*)
    rewrite Hmdata /encode_dbmods -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p) "Hxs".

    (*@     var data = bs1                                                      @*)
    (*@     var ents = make([]tulip.WriteEntry, 0, n)                           @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".
    wp_apply (wp_NewSliceWithCap (V:= dbmod)); first word.
    iIntros (entsbaseP) "Hents".
    wp_apply wp_ref_to; first done.
    iIntros (entsP) "HentsP".

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < n {                                                         @*)
    (*@         x, bsloop := DecodeWriteEntry(data)                             @*)
    (*@         ents = append(ents, x)                                          @*)
    (*@         data = bsloop                                                   @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    wp_pures.
    set P := (λ cont : bool, ∃ (i : u64) (p1 p2 : Slice.t),
                 let remaining := encode_dbmods_xlen (drop (uint.nat i) xs) ++ bstail in
                 "HdataP"  ∷ dataP ↦[slice.T byteT] p1 ∗
                 "HentsP"  ∷ entsP ↦[slice.T (struct.t WriteEntry)] p2 ∗
                 "HiP"     ∷ iP ↦[uint64T] #i ∗
                 "Hxs"     ∷ own_slice_small p1 byteT (DfracOwn 1) remaining ∗
                 "Hents"   ∷ own_slice p2 (struct.t WriteEntry) (DfracOwn 1) (take (uint.nat i) xs) ∗
                 "%Hbound" ∷ ⌜cont || bool_decide (length xs ≤ uint.nat i)%nat⌝)%I.
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
      assert (is_Some (xs !! uint.nat i)) as [x Hx].
      { apply lookup_lt_is_Some_2. word. }
      rewrite (drop_S _ _ _ Hx) encode_dbmods_xlen_cons -app_assoc.
      wp_apply (wp_DecodeWriteEntry with "Hxs").
      iIntros (bsloopP) "Hbsloop".
      wp_load.
      wp_apply (wp_SliceAppend with "Hents").
      iIntros (entsP') "Hents".
      do 2 wp_store. wp_load. wp_store.
      iApply "HΦ".
      iFrame "∗ %".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hx).
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

End program.
