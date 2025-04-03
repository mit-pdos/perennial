From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import decode_string.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_DecodeStrings (bsP : Slice.t) (strs : list byte_string) (bstail : list u8) :
    {{{ own_slice_small bsP byteT (DfracOwn 1) (encode_strings strs ++ bstail) }}}
      DecodeStrings (to_val bsP)
    {{{ (strsP : Slice.t) (dataP : Slice.t), RET (to_val strsP, to_val dataP);
        own_slice strsP stringT (DfracOwn 1) strs ∗
        own_slice_small dataP byteT (DfracOwn 1) bstail
    }}}.
  Proof.
    iIntros (Φ) "Hbs HΦ".
    wp_rec.
    iDestruct (own_slice_small_sz with "Hbs") as %Hlenbs.
    assert (Hlenstrs : length strs < 2 ^ 64).
    { rewrite length_app in Hlenbs.
      assert (Hlen : (length (encode_strings strs) ≤ uint.nat bsP.(Slice.sz))%nat) by lia.
      apply encode_strings_length_inv in Hlen.
      word.
    }

    (*@ func DecodeStrings(bs []byte) ([]string, []byte) {                      @*)
    (*@     n, bs1 := marshal.ReadInt(bs)                                       @*)
    (*@                                                                         @*)
    rewrite /encode_strings -app_assoc.
    wp_apply (wp_ReadInt with "Hbs").
    iIntros (p) "Hp".

    (*@     var data = bs1                                                      @*)
    (*@     var ents = make([]string, 0, n)                                     @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".
    wp_apply wp_NewSliceWithCap; first word.
    iIntros (entsbaseP) "Hents".
    wp_apply wp_ref_to; first done.
    iIntros (entsP) "HentsP".

    (*@     var i uint64 = 0                                                    @*)
    (*@     for i < n {                                                         @*)
    (*@         s, bsloop := DecodeString(data)                                 @*)
    (*@         ents = append(ents, s)                                          @*)
    (*@         data = bsloop                                                   @*)
    (*@         i++                                                             @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    wp_apply wp_ref_to; first by auto.
    iIntros (iP) "HiP".
    wp_pures.
    set P := (λ cont : bool, ∃ (i : u64) (p1 p2 : Slice.t),
                 let remaining := encode_strings_xlen (drop (uint.nat i) strs) ++ bstail in
                 "HdataP"  ∷ dataP ↦[slice.T byteT] p1 ∗
                 "HentsP"  ∷ entsP ↦[slice.T stringT] p2 ∗
                 "HiP"     ∷ iP ↦[uint64T] #i ∗
                 "Hstrs"   ∷ own_slice_small p1 byteT (DfracOwn 1) remaining ∗
                 "Hents"   ∷ own_slice p2 stringT (DfracOwn 1) (take (uint.nat i) strs) ∗
                 "%Hbound" ∷ ⌜cont || bool_decide (length strs ≤ uint.nat i)%nat⌝)%I.
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
      assert (is_Some (strs !! uint.nat i)) as [s Hs].
      { apply lookup_lt_is_Some_2. word. }
      rewrite (drop_S _ _ _ Hs) encode_strings_xlen_cons -app_assoc.
      wp_apply (wp_DecodeString with "Hstrs").
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

End program.
