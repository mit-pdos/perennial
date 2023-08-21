From Perennial.program_proof Require Import grove_prelude marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_map map.impl.
From Goose.github_com.mit_pdos.gokv Require Import map_string_marshal.

Section map_string_marshal_proof.

Context `{!heapGS Σ}.

Local Definition encode_maplist (l:list (string * string)) : list u8 :=
  flat_map (λ u,
              (u64_le (int.Z (length (string_to_bytes u.1)))) ++
              (string_to_bytes u.1) ++
              (u64_le (int.Z (length (string_to_bytes u.2)))) ++
              (string_to_bytes u.2)) l.

Local Lemma encode_maplist_cons k data l :
  encode_maplist ((k, data)::l) =
              ((u64_le $ int.Z $ length $ string_to_bytes k) ++
               (string_to_bytes k) ++
               (u64_le $ int.Z $ length $ string_to_bytes data) ++
               (string_to_bytes data)) ++ encode_maplist l.
Proof. done. Qed.

Local Definition has_partial_map_encoding (enc:list u8) (fullsize: u64) (m:gmap string string) : Prop :=
  ∃ l,
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  enc = (u64_le fullsize) ++ encode_maplist l.

Definition has_string_map_encoding (enc:list u8) (m:gmap string string) : Prop :=
  int.Z (size m) = size m ∧ has_partial_map_encoding enc (size m) m.

Lemma wp_EncodeStringMap mptr m :
  {{{
        "Hmap" ∷ own_map mptr 1 m
  }}}
    EncodeStringMap #mptr
  {{{
        enc_sl enc, RET (slice_val enc_sl);
        own_map mptr 1 m ∗
        own_slice enc_sl byteT 1 enc ∗
        ⌜has_string_map_encoding enc m⌝
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". iNamed "Hmap". wp_call.
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  (*
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
      "Hs" ∷ own_slice s byteT 1 enc
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
  wp_load. iApply "HΦ". iFrame. iSplitL.
  { iExists _. iFrame. eauto. }
  iPureIntro. split.
  - rewrite -size_dom -Hkvs_dom size_dom. rewrite Hmsize. word.
  - replace m with (map_zip_with (λ (v : list u8) (_ : Slice.t), v) m kvs_sl) at 2. 1:done.
    clear Henc. rewrite -[map_zip_with _ _ _]map_fmap_id. rewrite map_fmap_zip_with_l; auto.
    intros k. rewrite -!elem_of_dom. set_solver. *)
Admitted.

Lemma wp_DecodeStringMap enc_sl enc enc_rest q m :
  {{{
        "%Henc" ∷ ⌜has_string_map_encoding enc m⌝ ∗
        "Henc_sl" ∷ own_slice_small enc_sl byteT q (enc ++ enc_rest)
  }}}
    DecodeStringMap (slice_val enc_sl)
  {{{
        mptr, RET #mptr; own_map mptr 1 m
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". wp_call.
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  (*
  wp_apply wp_byteMapNew. iIntros (mptr) "Hm".
  wp_load.
  destruct Henc as [Hsz (ls & Hnodup & Hls & Henc)]. subst enc.
  rewrite -!app_assoc.
  wp_apply (wp_ReadInt with "Henc_sl"). iIntros (s') "Hs". wp_store. clear enc_sl.
  wp_apply wp_ref_to; first by val_ty. iIntros (li) "Hli". wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ s,
              "Hm" ∷ own_byte_map mptr (list_to_map (take (int.nat i) ls)) ∗
              "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
              "Hs" ∷ own_slice_small s byteT q (encode_byte_maplist (drop (int.nat i) ls) ++ enc_rest)
  )%I with "[] [$Hli Hm Hl Hs]"); first word.
  2:{ iExists _. iFrame. }
  { (* core loop *)
    clear s' Φ. iIntros (i Φ) " !#(I & Hli & %Hi) HΦ". iNamed "I". wp_lam.
    replace (int.nat (u64_instance.u64.(word.add) i 1)) with (1 + int.nat i)%nat by word.
    assert (is_Some (ls !! (int.nat i))) as [[k data] Hk].
    { apply lookup_lt_is_Some_2. rewrite -Map.size_list_to_map //.
      rewrite Hls. word. }
    rewrite -(take_drop_middle _ _ _ Hk) in Hls Hnodup.
    move:Hnodup. clear Hls.
    erewrite take_S_r by done.
    rewrite (drop_S _ _ _ Hk).
    set ls_head := take (int.nat i) ls.
    set ls_tail := drop (1+int.nat i) ls.
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
  done. *)
Admitted.

End map_string_marshal_proof.
