From Perennial.program_proof.tulip.program Require Import prelude.
From Perennial.program_proof.tulip.program.util Require Import encode_write_entry.
From Perennial.program_proof Require Import marshal_stateless_proof.

Section program.
  Context `{!heapGS Σ, !paxos_ghostG Σ}.

  Theorem wp_EncodeKVMap (bsP : Slice.t) (mP : loc) (bs : list u8) q (m : dbmap) :
    {{{ own_slice bsP byteT (DfracOwn 1) bs ∗ own_map mP q m }}}
      EncodeKVMap (to_val bsP) #mP
    {{{ (dataP : Slice.t) (mdata : list u8), RET (to_val dataP);
        own_slice dataP byteT (DfracOwn 1) (bs ++ mdata) ∗ own_map mP q m ∗
        ⌜encode_dbmap m mdata⌝
    }}}.
  Proof.
    iIntros (Φ) "[Hbs Hm] HΦ".
    wp_rec.

    (*@ func EncodeKVMap(bs []byte, m tulip.KVMap) []byte {                     @*)
    (*@     var data = marshal.WriteInt(bs, uint64(len(m)))                     @*)
    (*@                                                                         @*)
    wp_apply (wp_MapLen with "Hm").
    iIntros "[%Hszm Hm]".
    wp_apply (wp_WriteInt with "Hbs").
    iIntros (p) "Hp".
    wp_apply wp_ref_to; first done.
    iIntros (dataP) "HdataP".

    (*@     for k, v := range(m) {                                              @*)
    (*@         x := tulip.WriteEntry{                                          @*)
    (*@             Key   : k,                                                  @*)
    (*@             Value : v,                                                  @*)
    (*@         }                                                               @*)
    (*@         data = EncodeWriteEntry(data, x)                                @*)
    (*@     }                                                                   @*)
    (*@                                                                         @*)
    set P := (λ (mx : dbmap), ∃ (px : Slice.t) (ml : list dbmod),
                 let l := encode_dbmods_xlen ml in
                "HdataP" ∷ dataP ↦[slice.T byteT] px ∗
                "Hdata"  ∷ own_slice px byteT (DfracOwn 1) (bs ++ u64_le (W64 (size m)) ++ l) ∗
                "%Hml"   ∷ ⌜ml ≡ₚ map_to_list mx⌝)%I.
    wp_apply (wp_MapIter_fold _ _ _ P with "Hm [-HΦ]").
    { iExists _, []. rewrite map_to_list_empty.
      rewrite /encode_dbmods_xlen /serialize.serialize.
      list_simplifier. by iFrame. }
    { clear Φ.
      iIntros (mx k v Φ) "!> [HP %Hk] HΦ".
      destruct Hk as [Hmxk Hmk].
      iNamed "HP".
      wp_load.
      wp_apply (wp_EncodeWriteEntry _ (k, v) with "Hdata").
      iIntros (py) "Hdata".
      wp_store.
      iApply "HΦ".
      rewrite -2!(app_assoc _ _ (encode_dbmod (k, v))).
      iExists _, (ml ++ [(k, v)]).
      rewrite encode_dbmods_xlen_snoc.
      iFrame.
      iPureIntro.
      rewrite map_to_list_insert; last apply Hmxk.
      rewrite Hml.
      symmetry.
      apply Permutation_cons_append.
    }
    iIntros "[Hm HP]".
    iNamed "HP".
    wp_load.

    (*@     return data                                                         @*)
    (*@ }                                                                       @*)
    iApply "HΦ".
    iFrame.
    iPureIntro.
    exists ml.
    split; last done.
    rewrite /encode_dbmods.
    do 2 f_equal.
    by rewrite Hml length_map_to_list.
  Qed.

End program.
