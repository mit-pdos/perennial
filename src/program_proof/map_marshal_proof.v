From Perennial.program_proof Require Import grove_prelude marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_map map.impl.
From Goose.github_com.mit_pdos.gokv Require Import map_marshal.

Section map_marshal_proof.

Context `{!heapGS Σ}.
Definition own_byte_map (mptr:loc) (m:gmap u64 (list u8)): iProp Σ :=
  ∃ (kvs_sl:gmap u64 Slice.t),
    "Hkvs_map" ∷ own_map mptr (DfracOwn 1) kvs_sl ∗
    "%Hkvs_dom" ∷ ⌜dom kvs_sl = dom m⌝ ∗
    "#Hkvs_slices" ∷ (∀ (k:u64),
        readonly (own_slice_small (default Slice.nil (kvs_sl !! k))
                    byteT
                    (DfracOwn 1)
                    (default [] (m !! k))
                 )
      )
.

Lemma wp_byteMapNew :
  {{{
        True
  }}}
    NewMap uint64T (slice.T byteT) #()
  {{{
        mptr, RET #mptr; own_byte_map mptr ∅
  }}}.
Proof.
  iIntros (Φ) "_ HΦ".

  iDestruct (own_slice_small_nil byteT (DfracOwn 1) Slice.nil) as "HH".
  { done. }
  iMod (readonly_alloc_1 with "HH") as "Hsl".
  wp_apply (wp_NewMap).
  iIntros (?) "Hmap".
  iApply "HΦ".
  iExists _; iFrame.
  iSplitR.
  { rewrite !dom_empty_L. done. }
  iIntros (?).
  rewrite lookup_empty.
  rewrite lookup_empty.
  simpl.
  iFrame "Hsl".
Qed.

Lemma wp_byteMapGet mptr m (k:u64) :
  {{{ own_byte_map mptr m }}}
    Fst (MapGet #mptr #k)
  {{{
        sl, RET (slice_val sl);
        readonly (own_slice_small sl byteT (DfracOwn 1) (default [] (m !! k))) ∗
        own_byte_map mptr m
  }}}
.
Proof.
  iIntros (Φ) "Hmap HΦ".
  iNamed "Hmap".
  wp_apply (wp_MapGet with "Hkvs_map").
  iIntros (sl ok) "[%Hlookup Hkvs_map]".
  wp_pures.
  iApply "HΦ".
  iSplitR "Hkvs_map"; last first.
  { iExists _. eauto with iFrame. }
  iModIntro.
  iSpecialize ("Hkvs_slices" $! k).
  rewrite /map_get in Hlookup.
  apply (f_equal fst) in Hlookup.
  simpl in Hlookup.
  rewrite Hlookup.
  iFrame "#".
Qed.

Lemma wp_byteMapPut mptr m (k:u64) sl (v:list u8) q :
{{{
      own_byte_map mptr m ∗ own_slice_small sl byteT (DfracOwn q) v
}}}
    MapInsert #mptr #k (slice_val sl)
{{{
      RET #(); own_byte_map mptr (<[k := v]> m)
}}}
.
Proof.
  iIntros (Φ) "[Hmap Hsl] HΦ".
  iNamed "Hmap".
  iMod (readonly_alloc (own_slice_small sl byteT (DfracOwn 1) v) with "[Hsl]") as "#Hsl".
  { done. }
  wp_apply (wp_MapInsert with "Hkvs_map").
  { done. }
  iIntros "Hkvs_map".
  iApply "HΦ".
  iExists _.
  iFrame "Hkvs_map".
  rewrite /typed_map.map_insert.
  iSplitR.
  { rewrite !dom_insert_L Hkvs_dom. done. }
  iIntros (?).
  destruct (decide (k0 = k)).
  {
    rewrite e.
    repeat rewrite lookup_insert.
    simpl.
    done.
  }
  {
    rewrite lookup_insert_ne; last done.
    rewrite lookup_insert_ne; last done.
    iApply "Hkvs_slices".
  }
Qed.

Local Definition encode_byte_maplist (l:list (u64 * list u8)) : list u8 :=
  flat_map (λ u, (u64_le u.1) ++ (u64_le (uint.Z (length (u.2)))) ++ u.2) l.

Local Lemma encode_byte_maplist_cons k data l :
  encode_byte_maplist ((k, data)::l) = (u64_le k) ++ (u64_le (uint.Z (length data))) ++ data ++ encode_byte_maplist l.
Proof. done. Qed.

Local Definition has_partial_byte_map_encoding (enc:list u8) (fullsize: u64) (m:gmap u64 (list u8)) : Prop :=
  ∃ l,
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  enc = (u64_le fullsize) ++ encode_byte_maplist l.

Definition has_byte_map_encoding (enc:list u8) (m:gmap u64 (list u8)) : Prop :=
  uint.Z (size m) = size m ∧ has_partial_byte_map_encoding enc (size m) m.

Lemma wp_EncodeMapU64ToBytes mptr m :
  {{{
        "Hmap" ∷ own_byte_map mptr m
  }}}
    EncodeMapU64ToBytes #mptr
  {{{
        enc_sl enc, RET (slice_val enc_sl);
        own_byte_map mptr m ∗
        own_slice enc_sl byteT (DfracOwn 1) enc ∗
        ⌜has_byte_map_encoding enc m⌝
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". iNamed "Hmap". wp_call.
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_apply (wp_MapLen with "Hkvs_map"). iIntros "[%Hmsize Hkvs_map]".
  wp_load.
  wp_apply (wp_WriteInt with "Hs"). iIntros (s') "Hs".
  rewrite replicate_0 /=. wp_store. clear s.
  wp_apply (wp_MapIter_2 _ _ _ _ _
    (λ kvs_todo kvs_done, ∃ (s : Slice.t) enc,
      "%Hm" ∷ ⌜kvs_sl = kvs_todo ∪ kvs_done⌝ ∗
      "%Hdisk" ∷ ⌜dom kvs_todo ## dom kvs_done⌝ ∗
      "%Henc" ∷ ⌜has_partial_byte_map_encoding enc (size m) (map_zip_with (λ v _, v) m kvs_done)⌝ ∗
      "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
      "Hs" ∷ own_slice s byteT (DfracOwn 1) enc
    )%I with "Hkvs_map [Hl Hs]").
  { iExists _, _. iFrame. iPureIntro.
    rewrite right_id_L. split; first done.
    rewrite /has_partial_byte_map_encoding.
    split; first set_solver.
    exists [].
    split; first by apply NoDup_nil_2.
    rewrite map_zip_with_empty_r.
    split; first by apply list_to_map_nil.
    do 2 rewrite -size_dom. rewrite -Hkvs_dom size_dom. done. }
  { (* core loop *)
     clear Φ s' mptr. iIntros (k v kvs_todo kvs_done Φ) "!# [HI %Hk] HΦ". iNamed "HI". wp_pures.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (s') "Hs". wp_store. clear s.
     wp_apply wp_slice_len.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (s) "Hs". wp_store. clear s'.
     iSpecialize ("Hkvs_slices" $! k).
     iMod (readonly_load with "Hkvs_slices") as (q) "Hk".
     iDestruct (own_slice_small_sz with "Hk") as %Hsz.
     iEval (rewrite Hm) in "Hk".
     erewrite lookup_union_Some_l by done. simpl.
     wp_load. wp_apply (wp_WriteBytes with "[$Hs $Hk]"). iIntros (s') "[Hs _]". wp_store. clear s.
     iApply "HΦ". iModIntro. iExists _, _. iFrame. iPureIntro.
     split.
     { rewrite union_delete_insert //. }
     assert (kvs_done !! k = None).
     { apply not_elem_of_dom. apply elem_of_dom_2 in Hk. set_solver. }
     split; first set_solver.
     assert (is_Some (m !! k)) as [data Hdata].
     { apply elem_of_dom. rewrite -Hkvs_dom Hm dom_union. apply elem_of_dom_2 in Hk. set_solver. }
     destruct Henc as (ls & Hnodup & Hls & Henc). exists (ls ++ [(k, data)]).
     assert (k ∉ ls.*1).
     { intros Hin. eapply (not_elem_of_list_to_map ls). 2:by apply Hin.
       rewrite Hls. apply map_lookup_zip_with_None. auto. }
     split; last split.
     - rewrite fmap_app. apply NoDup_app. split; first done.
       simpl. split; last by apply NoDup_singleton.
       intros k' Hk' ->%elem_of_list_singleton. done.
     - rewrite list_to_map_snoc //. rewrite Hls.
       change data with ((λ v _, v) data v).
       rewrite map_insert_zip_with. rewrite insert_id //.
     - rewrite Hdata Henc. cbn. rewrite -!app_assoc. repeat f_equal.
       rewrite /encode_byte_maplist flat_map_app. f_equal. cbn. rewrite -!app_assoc app_nil_r. repeat f_equal.
       move:Hsz. rewrite Hdata Hm. erewrite lookup_union_Some_l by done. cbn. intros. word.
  }
  iIntros "[Hkvs_map HI]". iNamed "HI".
  wp_load. iApply "HΦ". iFrame. iSplitL; first eauto.
  iPureIntro. split.
  - rewrite -size_dom -Hkvs_dom size_dom. rewrite Hmsize. word.
  - replace m with (map_zip_with (λ (v : list u8) (_ : Slice.t), v) m kvs_sl) at 2. 1:done.
    clear Henc. rewrite -[map_zip_with _ _ _]map_fmap_id. rewrite map_fmap_zip_with_l; auto.
    intros k. rewrite -!elem_of_dom. set_solver.
Qed.

Lemma wp_DecodeMapU64ToBytes m enc_sl enc enc_rest q :
  {{{
        "%Henc" ∷ ⌜has_byte_map_encoding enc m⌝ ∗
        "Henc_sl" ∷ own_slice_small enc_sl byteT (DfracOwn q) (enc ++ enc_rest)
  }}}
    DecodeMapU64ToBytes (slice_val enc_sl)
  {{{
        rest_enc_sl q' mptr, RET (#mptr, slice_val rest_enc_sl);
        own_byte_map mptr m ∗
        own_slice_small rest_enc_sl byteT (DfracOwn q') enc_rest
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". wp_call.
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_apply wp_byteMapNew. iIntros (mptr) "Hm".
  wp_load.
  destruct Henc as [Hsz (ls & Hnodup & Hls & Henc)]. subst enc.
  rewrite -!app_assoc.
  wp_apply (wp_ReadInt with "Henc_sl"). iIntros (s') "Hs". wp_store. clear enc_sl.
  wp_apply wp_ref_to; first by val_ty. iIntros (li) "Hli". wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ s,
              "Hm" ∷ own_byte_map mptr (list_to_map (take (uint.nat i) ls)) ∗
              "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
              "Hs" ∷ own_slice_small s byteT (DfracOwn q) (encode_byte_maplist (drop (uint.nat i) ls) ++ enc_rest)
  )%I with "[] [$Hli Hm Hl Hs]"); first word.
  2:{ iExists _. iFrame. }
  { (* core loop *)
    clear s' Φ. iIntros (i Φ) " !#(I & Hli & %Hi) HΦ". iNamed "I". wp_lam.
    replace (uint.nat (word.add i 1)) with (1 + uint.nat i)%nat by word.
    assert (is_Some (ls !! (uint.nat i))) as [[k data] Hk].
    { apply lookup_lt_is_Some_2. rewrite -Map.size_list_to_map //.
      rewrite Hls. word. }
    rewrite -(take_drop_middle _ _ _ Hk) in Hls Hnodup.
    move:Hnodup. clear Hls.
    erewrite take_S_r by done.
    rewrite (drop_S _ _ _ Hk).
    set ls_head := take (uint.nat i) ls.
    set ls_tail := drop (1+uint.nat i) ls.
    intros Hnodup.
    rewrite encode_byte_maplist_cons -!app_assoc.
    wp_load.
    wp_apply (wp_ReadInt with "Hs"). iIntros (s') "Hs".
    wp_apply (wp_ReadInt with "Hs"). iIntros (s'') "Hs".
    iDestruct (own_slice_small_sz with "Hs") as %Hdatasz.
    wp_apply (wp_ReadBytesCopy with "Hs").
    { rewrite !app_length in Hdatasz. word. }
    iIntros (sl s''') "[Hval Hs]". wp_store. clear s s' s'' Hdatasz.
    wp_apply (wp_byteMapPut with "[$Hm Hval]").
    { iDestruct (own_slice_to_small with "Hval") as "$". }
    iIntros "Hm". wp_pures. iApply "HΦ". iModIntro.
    iFrame "Hli". iExists _. iFrame. iExactEq "Hm". rewrite /named. f_equal.
    rewrite list_to_map_snoc //.
    rewrite fmap_app NoDup_app in Hnodup.
    destruct Hnodup as (_ & Hnin & _). intros Hin. eapply Hnin; first done.
    eapply elem_of_list_fmap_1_alt.
    - apply elem_of_list_here.
    - done. }
  iIntros "(I & Hli)". iNamed "I". wp_load. wp_pures. iApply "HΦ". iModIntro.
  rewrite take_ge.
  2:{ rewrite -Map.size_list_to_map // Hls. word. }
  rewrite Hls. iFrame "Hm".
  rewrite drop_ge.
  2:{ rewrite -Map.size_list_to_map // Hls. word. }
  done.
Qed.

Local Definition encode_u64_maplist (l:list (u64 * u64)) : list u8 :=
  flat_map (λ u, (u64_le u.1) ++ (u64_le u.2)) l.

Local Lemma encode_u64_maplist_cons k data l :
  encode_u64_maplist ((k, data)::l) = (u64_le k) ++ (u64_le data) ++ encode_u64_maplist l.
Proof. done. Qed.

Local Definition has_partial_u64_map_encoding (enc:list u8) (fullsize: u64) (m:gmap u64 u64) : Prop :=
  ∃ l,
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  enc = (u64_le fullsize) ++ encode_u64_maplist l.

Definition has_u64_map_encoding (enc:list u8) (m:gmap u64 u64) : Prop :=
  (uint.Z (size m) = size m) ∧ has_partial_u64_map_encoding enc (size m) m.

Lemma wp_EncodeMapU64ToU64 mptr m :
  {{{
        "Hmap" ∷ own_map mptr (DfracOwn 1) m
  }}}
    EncodeMapU64ToU64 #mptr
  {{{
        enc_sl enc, RET (slice_val enc_sl);
        own_map mptr (DfracOwn 1) m ∗
        own_slice enc_sl byteT (DfracOwn 1) enc ∗
        ⌜has_u64_map_encoding enc m⌝
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". wp_call.
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_apply (wp_MapLen with "Hmap"). iIntros "[%Hmsize Hmap]".
  wp_load.
  wp_apply (wp_WriteInt with "Hs"). iIntros (s') "Hs".
  rewrite replicate_0 /=. wp_store. clear s.
  wp_apply (wp_MapIter_2 _ _ _ _ _
    (λ mtodo mdone, ∃ (s : Slice.t) enc,
      "%Hm" ∷ ⌜m = mtodo ∪ mdone⌝ ∗
      "%Hdisk" ∷ ⌜dom mtodo ## dom mdone⌝ ∗
      "%Henc" ∷ ⌜has_partial_u64_map_encoding enc (size m) mdone⌝ ∗
      "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
      "Hs" ∷ own_slice s byteT (DfracOwn 1) enc
    )%I with "Hmap [Hl Hs]").
  { iExists _, _. iFrame. iPureIntro.
    rewrite right_id_L. split; first done.
    rewrite /has_partial_u64_map_encoding.
    split; first set_solver.
    exists [].
    split; first by apply NoDup_nil_2.
    split; first by apply list_to_map_nil.
    done. }
  { (* core loop *)
     clear Φ s' mptr. iIntros (k v mtodo mdone Φ) "!# [HI %Hk] HΦ". iNamed "HI". wp_pures.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (s') "Hs". wp_store. clear s.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (s) "Hs". wp_store. clear s'.
     iApply "HΦ". iModIntro. iExists _, _. iFrame. iPureIntro.
     split.
     { rewrite union_delete_insert //. }
     assert (mdone !! k = None).
     { apply not_elem_of_dom. apply elem_of_dom_2 in Hk. set_solver. }
     split; first set_solver.
     assert (m !! k = Some v) as Hkm.
     { rewrite Hm lookup_union_l //. }
     destruct Henc as (ls & Hnodup & Hls & Henc). exists (ls ++ [(k, v)]).
     assert (k ∉ ls.*1).
     { intros Hin. eapply (not_elem_of_list_to_map ls). 2:by apply Hin.
       rewrite Hls. auto. }
     split; last split.
     - rewrite fmap_app. apply NoDup_app. split; first done.
       simpl. split; last by apply NoDup_singleton.
       intros k' Hk' ->%elem_of_list_singleton. done.
     - rewrite list_to_map_snoc //. rewrite Hls //.
     - rewrite Henc. rewrite -!app_assoc. repeat f_equal.
       rewrite /encode_u64_maplist flat_map_app. f_equal.
  }
  iIntros "[Hkvs_map HI]". iNamed "HI".
  wp_load. iApply "HΦ". iFrame.
  iPureIntro. split.
  - rewrite Hmsize. word.
  - done.
Qed.

Lemma wp_DecodeMapU64ToU64 m enc_sl enc enc_rest q :
  {{{
        "%Henc" ∷ ⌜has_u64_map_encoding enc m⌝ ∗
        "Henc_sl" ∷ own_slice_small enc_sl byteT (DfracOwn q) (enc ++ enc_rest)
  }}}
    DecodeMapU64ToU64 (slice_val enc_sl)
  {{{
        rest_enc_sl q' mptr, RET (#mptr, slice_val rest_enc_sl);
        own_map mptr (DfracOwn 1) m ∗
        own_slice_small rest_enc_sl byteT (DfracOwn q') enc_rest
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". wp_call.
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_apply wp_NewMap. iIntros (mptr) "Hm".
  wp_load.
  destruct Henc as [Hsz (ls & Hnodup & Hls & Henc)]. subst enc.
  rewrite -!app_assoc.
  wp_apply (wp_ReadInt with "Henc_sl"). iIntros (s') "Hs". wp_store. clear enc_sl.
  wp_apply wp_ref_to; first by val_ty. iIntros (li) "Hli". wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ s,
              "Hm" ∷ own_map mptr (DfracOwn 1) (list_to_map (take (uint.nat i) ls)) ∗
              "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
              "Hs" ∷ own_slice_small s byteT (DfracOwn q) (encode_u64_maplist (drop (uint.nat i) ls) ++ enc_rest)
  )%I with "[] [$Hli Hm Hl Hs]"); first word.
  2:{ iExists _. iFrame. }
  { (* core loop *)
    clear s' Φ. iIntros (i Φ) " !#(I & Hli & %Hi) HΦ". iNamed "I". wp_lam.
    replace (uint.nat (word.add i 1)) with (1 + uint.nat i)%nat by word.
    assert (is_Some (ls !! (uint.nat i))) as [[k data] Hk].
    { apply lookup_lt_is_Some_2. rewrite -Map.size_list_to_map //.
      rewrite Hls. word. }
    rewrite -(take_drop_middle _ _ _ Hk) in Hls Hnodup.
    move:Hnodup. clear Hls.
    erewrite take_S_r by done.
    rewrite (drop_S _ _ _ Hk).
    set ls_head := take (uint.nat i) ls.
    set ls_tail := drop (1+uint.nat i) ls.
    intros Hnodup.
    rewrite encode_u64_maplist_cons -!app_assoc.
    wp_apply wp_ref_of_zero. { done. } iIntros (lkey) "?".
    wp_apply wp_ref_of_zero. { done. } iIntros (lval) "?".
    wp_load.
    wp_apply (wp_ReadInt with "Hs"). iIntros (s') "Hs".
    do 2 wp_store.
    wp_load.
    wp_apply (wp_ReadInt with "Hs"). iIntros (s'') "Hs".
    do 2 wp_store.
    do 2 wp_load.
    wp_apply (wp_MapInsert with "[$Hm]").
    { done. }
    rewrite /map_insert.
    iIntros "Hm". wp_pures. iApply "HΦ". iModIntro.
    iFrame "Hli". iExists _. iFrame. iExactEq "Hm". rewrite /named. f_equal.
    rewrite list_to_map_snoc //.
    rewrite fmap_app NoDup_app in Hnodup.
    destruct Hnodup as (_ & Hnin & _). intros Hin. eapply Hnin; first done.
    eapply elem_of_list_fmap_1_alt.
    - apply elem_of_list_here.
    - done. }
  iIntros "(I & Hli)". iNamed "I". wp_load. wp_pures. iApply "HΦ". iModIntro.
  rewrite take_ge.
  2:{ rewrite -Map.size_list_to_map // Hls. word. }
  rewrite Hls. iFrame "Hm".
  rewrite drop_ge.
  2:{ rewrite -Map.size_list_to_map // Hls. word. }
  done.
Qed.

End map_marshal_proof.
