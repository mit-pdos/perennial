From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_write_entry.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeKVMap
    (bsP : Slice.t) (m : dbmap) (mdata : list u8) (bstail : list u8) :
    encode_dbmap m mdata ->
    {{{ own_slice_small bsP byteT (DfracOwn 1) (mdata ++ bstail) }}}
      DecodeKVMap (to_val bsP)
    {{{ (mP : loc) (dataP : Slice.t), RET (#mP, to_val dataP);
        own_map mP (DfracOwn 1) m ∗
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

    (*@ func DecodeKVMap(bs []byte) (tulip.KVMap, []byte) {                     @*)
    (*@     n, bs1 := marshal.ReadInt(bs)                                       @*)
    (*@                                                                         @*)
    rewrite Hmdata /encode_dbmods -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p) "Hxs".

    (*@     var data = bs1                                                      @*)
    (*@     m := make(map[string]tulip.Value)                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".
    wp_apply (wp_NewMap dbkey dbval).
    iIntros (mP) "Hm".

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < n {                                                         @*)
    (*@         x, bsloop := DecodeWriteEntry(data)                             @*)
    (*@         m[x.Key] = x.Value                                              @*)
    (*@         data = bsloop                                                   @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    wp_pures.
    set P := (λ cont : bool, ∃ (i : u64) (p1 : Slice.t),
                 let remaining := encode_dbmods_xlen (drop (uint.nat i) xs) ++ bstail in
                 "HdataP"  ∷ dataP ↦[slice.T byteT] p1 ∗
                 "Hm"      ∷ own_map mP (DfracOwn 1) (list_to_map (take (uint.nat i) xs)) ∗
                 "HiP"     ∷ iP ↦[uint64T] #i ∗
                 "Hxs"     ∷ own_slice_small p1 byteT (DfracOwn 1) remaining ∗
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
      wp_pures.
      wp_apply (wp_MapInsert with "Hm"); first done.
      iIntros "Hm".
      wp_store. wp_load. wp_store.
      iApply "HΦ".
      iFrame "∗ %".
      rewrite uint_nat_word_add_S; last word.
      rewrite (take_S_r _ _ _ Hx).
      iFrame.
      destruct x as [t v].
      rewrite list_to_map_snoc; first done.
      rewrite fmap_take.
      apply not_elem_of_take.
      { rewrite Hxs. apply NoDup_fst_map_to_list. }
      apply list_lookup_fmap_Some.
      eexists (_, _); split; eauto.
    }
    iNamed 1.
    case_bool_decide as Hi; last done.
    wp_load.
    wp_pures.

    (*@     return m, data                                                      @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    rewrite take_ge; last apply Hi.
    rewrite drop_ge; last apply Hi.
    symmetry in Hxs. apply list_to_map_flip in Hxs.
    rewrite -Hxs.
    by iFrame.
  Qed.

End program.
