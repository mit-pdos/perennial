From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeString (bsP : Slice.t) (s : string) (bs : list u8) :
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
    by rewrite -app_assoc /encode_string string_bytes_length.
  Qed.

  Theorem wp_DecodeString (bsP : Slice.t) (s : string) (bstail : list u8) :
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
    rewrite string_to_bytes_to_string.
    by iApply "HΦ".
  Qed.

  Theorem wp_EncodeStrings
    (bsP : Slice.t) (strsP : Slice.t) (bs : list u8) (strs : list string) :
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
    wp_apply (wp_forSlice P with "[] [$Hstrs $Hp $HdataP]"); last first; first 1 last.
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
      by rewrite (take_S_r _ _ _ Hs) encode_strings_xlen_snoc -app_assoc.
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

  Theorem wp_DecodeStrings (bsP : Slice.t) (strs : list string) (bstail : list u8) :
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
      rewrite Z_u64; last first.
      { clear -Hlenstrs. lia. }
      set b := bool_decide _.
      destruct b eqn:Hb; wp_pures; last first.
      { iApply "HΦ".
        iFrame.
        iPureIntro.
        subst b.
        case_bool_decide as Hi; first done.
        apply bool_decide_pack.
        lia.
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
