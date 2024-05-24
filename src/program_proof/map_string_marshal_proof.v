From Perennial.program_proof Require Import grove_prelude marshal_stateless_proof.
From Perennial.goose_lang.lib Require Import typed_map map.impl.
From Goose.github_com.mit_pdos.gokv Require Import map_string_marshal.

Section map_string_marshal_proof.

Context `{!heapGS Σ}.

Local Definition encode_maplist (l:list (string * string)) : list u8 :=
  flat_map (λ u,
              (u64_le (String.length u.1)) ++
              (string_to_bytes u.1) ++
              (u64_le (String.length u.2)) ++
              (string_to_bytes u.2)) l.

Local Lemma encode_maplist_cons k data l :
  encode_maplist ((k, data)::l) =
              ((u64_le $ String.length k) ++
               (string_to_bytes k) ++
               (u64_le $ String.length $ data) ++
               (string_to_bytes data)) ++ encode_maplist l.
Proof. done. Qed.

Local Definition has_partial_map_encoding (enc:list u8) (fullsize: u64) (m:gmap string string) : Prop :=
  ∃ l,
  NoDup l.*1 ∧
  (list_to_map l) = m ∧
  enc = (u64_le fullsize) ++ encode_maplist l.

Definition has_string_map_encoding (enc:list u8) (m:gmap string string) : Prop :=
  uint.Z (size m) = size m ∧ has_partial_map_encoding enc (size m) m.

Lemma wp_EncodeStringMap mptr m :
  {{{
        "Hmap" ∷ own_map mptr (DfracOwn 1) m
  }}}
    EncodeStringMap #mptr
  {{{
        enc_sl enc, RET (slice_val enc_sl);
        own_map mptr (DfracOwn 1) m ∗
        own_slice enc_sl byteT (DfracOwn 1) enc ∗
        ⌜has_string_map_encoding enc m⌝
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". iNamed "Hmap". wp_call.
  wp_apply wp_NewSlice. iIntros (s) "Hs".
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_pures.
  wp_apply (wp_MapLen with "Hmap"). iIntros "[%Hmsize Hmap]".
  wp_load.
  wp_apply (wp_WriteInt with "Hs"). iIntros (s') "Hs".
  rewrite replicate_0 /=. wp_store. clear s.
  wp_apply (wp_MapIter_2 _ _ _ _ _
    (λ m_todo m_done, ∃ (s : Slice.t) enc,
      "%Hm" ∷ ⌜m = m_todo ∪ m_done⌝ ∗
      "%Hdisk" ∷ ⌜dom m_todo ## dom m_done⌝ ∗
      "%Henc" ∷ ⌜ has_partial_map_encoding enc (size m) (map_zip_with (λ v _, v) m m_done)⌝ ∗
      "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
      "Hs" ∷ own_slice s byteT (DfracOwn 1) enc
    )%I with "Hmap [Hl Hs]").
  { iExists _, _. iFrame. iPureIntro.
    rewrite right_id_L. split; first done.
    rewrite /has_partial_map_encoding.
    split; first set_solver.
    exists [].
    split; first by apply NoDup_nil_2.
    rewrite map_zip_with_empty_r.
    split; first by apply list_to_map_nil.
    rewrite Hmsize. done. }
  { (* core loop *)
     clear Φ s' mptr. iIntros (k v m_todo m_done Φ) "!# [HI %Hk] HΦ". iNamed "HI". wp_pures.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (?) "Hs". wp_store. clear s.
     wp_apply wp_StringToBytes.
     iIntros (?) "Hksl". iDestruct (own_slice_to_small with "Hksl") as "Hksl".
     wp_load.
     wp_apply (wp_WriteBytes with "[$Hs $Hksl]").
     iIntros (?) "[Hs _]".
     wp_store.
     wp_load. wp_apply (wp_WriteInt with "Hs"). iIntros (?) "Hs". wp_store. clear s' s'0.
     wp_pures.
     wp_apply wp_StringToBytes.
     iIntros (?) "Hvsl". iDestruct (own_slice_to_small with "Hvsl") as "Hvsl".
     wp_load.
     wp_apply (wp_WriteBytes with "[$Hs $Hvsl]").
     iIntros (?) "[Hs _]".
     wp_store.
     iApply "HΦ".
     iModIntro.
     repeat iExists _; iFrame.
     iPureIntro.
     split.
     { rewrite union_delete_insert //. }
     assert (m_done !! k = None).
     { apply not_elem_of_dom. apply elem_of_dom_2 in Hk. set_solver. }
     split; first set_solver.
     assert (is_Some (m !! k)) as [data Hdata].
     { apply elem_of_dom. rewrite Hm dom_union. apply elem_of_dom_2 in Hk. set_solver. }
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
     - subst. cbn. rewrite -!app_assoc. repeat f_equal.
       rewrite /encode_maplist flat_map_app. f_equal. cbn. rewrite -!app_assoc app_nil_r.
       rewrite lookup_union in Hdata. rewrite Hk union_Some_l in Hdata.
       injection Hdata as <-. done.
  }
  iIntros "[Hkvs_map HI]". iNamed "HI".
  wp_load. iApply "HΦ". iFrame.
  iPureIntro. split.
  - word.
  - rewrite -[map_zip_with _ _ _]map_fmap_id in Henc. rewrite map_fmap_zip_with_l in Henc; auto.
Qed.

Lemma wp_DecodeStringMap enc_sl enc enc_rest q m :
  {{{
        "%Henc" ∷ ⌜has_string_map_encoding enc m⌝ ∗
        "Henc_sl" ∷ own_slice_small enc_sl byteT q (enc ++ enc_rest)
  }}}
    DecodeStringMap (slice_val enc_sl)
  {{{
        mptr, RET #mptr; own_map mptr (DfracOwn 1) m
  }}}.
Proof.
  iIntros "%Φ H HΦ". iNamed "H". wp_call.
  wp_apply wp_ref_to; first by val_ty. iIntros (l) "Hl".
  wp_pures. wp_apply wp_ref_of_zero; first done.
  iIntros (?) "Hnum".
  wp_pures.
  wp_apply wp_NewMap. iIntros (mptr) "Hm".
  wp_load.
  destruct Henc as [Hsz (ls & Hnodup & Hls & Henc)]. subst enc.
  rewrite -!app_assoc.
  wp_apply (wp_ReadInt with "Henc_sl"). iIntros (s') "Hs". wp_pures.
  wp_store. wp_store. wp_load.
  wp_apply wp_ref_to; first by val_ty. iIntros (li) "Hli". wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ s q,
              "Hm" ∷ own_map mptr (DfracOwn 1) (list_to_map (take (uint.nat i) ls)) ∗
              "Hl" ∷ l ↦[slice.T byteT] (slice_val s) ∗
              "Hs" ∷ own_slice_small s byteT q (encode_maplist (drop (uint.nat i) ls) ++ enc_rest)
  )%I with "[] [$Hli Hm Hl Hs]"); first word.
  2:{ repeat iExists _. iFrame. }
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
    rewrite encode_maplist_cons -!app_assoc.
    wp_apply wp_ref_of_zero; first done.
    iIntros (?) "?".
    wp_pures.
    wp_apply wp_ref_of_zero; first done. iIntros (?) "?".
    wp_pures.
    wp_apply wp_ref_of_zero; first done. iIntros (?) "?".
    wp_pures.
    wp_load.
    wp_apply (wp_ReadInt with "Hs"). iIntros (s') "Hs".
    wp_pures. wp_store. wp_store.
    wp_load. wp_load.
    iDestruct (own_slice_small_sz with "Hs") as %Hsl_sz.
    wp_apply (wp_ReadBytes with "[$]").
    { rewrite string_bytes_length. rewrite app_length in Hsl_sz. word. }
    iIntros "* [Hksl Hs]".
    wp_pures. wp_store. wp_store. wp_load.
    wp_apply (wp_ReadInt with "Hs"). iIntros (?) "Hs".
    wp_pures. wp_store. wp_store.
    wp_load. wp_load. clear Hsl_sz.
    iDestruct (own_slice_small_sz with "Hs") as %Hsl_sz.
    wp_apply (wp_ReadBytes with "[$]").
    { rewrite string_bytes_length. rewrite app_length in Hsl_sz. word. }
    iIntros "* [Hvsl Hs]".
    wp_pures. wp_store. wp_store. wp_load.
    wp_apply (wp_StringFromBytes with "[$Hvsl]").
    iIntros "_".
    wp_load.
    wp_apply (wp_StringFromBytes with "[$Hksl]").
    iIntros "_".
    repeat rewrite string_to_bytes_inj.
    wp_apply (wp_MapInsert with "[$]").
    { done. }
    iIntros "Hm". wp_pures. iApply "HΦ". iModIntro.
    iFrame "Hli". repeat iExists _. iFrame. iExactEq "Hm". rewrite /named. f_equal.
    rewrite list_to_map_snoc //.
    rewrite fmap_app NoDup_app in Hnodup.
    destruct Hnodup as (_ & Hnin & _). intros Hin. eapply Hnin; first done.
    eapply elem_of_list_fmap_1_alt.
    - apply elem_of_list_here.
    - done. }
  iIntros "(I & Hli)". iNamed "I". wp_pures. iApply "HΦ". iModIntro.
  rewrite take_ge.
  2:{ rewrite -Map.size_list_to_map // Hls. word. }
  rewrite Hls. iFrame "Hm".
Qed.

End map_string_marshal_proof.
