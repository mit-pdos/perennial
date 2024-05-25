From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_coord_definitions common_proof.
From Perennial.program_proof.memkv Require Import memkv_shard_clerk_proof.

(* Needed for ShardClerkSet GetClerk *)
From Perennial.program_proof.memkv Require Import memkv_coord_clerk_proof.

Section memkv_coord_start_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_encodeShardMap s (shardMap_sl : Slice.t) (shardMapping : list u64) :
  length shardMapping = uint.nat uNSHARD →
  {{{ "Hs_ptr" ∷ s ↦[slice.T HostName] (slice_val shardMap_sl) ∗
      "HshardMap_sl" ∷ typed_slice.own_slice_small (V:=u64) shardMap_sl HostName (DfracOwn 1) shardMapping
  }}}
    encodeShardMap #s
  {{{ (sl: Slice.t) (data: list u8), RET (slice_val sl);
      "%Henc" ∷ ⌜ has_encoding_shardMapping data shardMapping ⌝ ∗
      "Hdata" ∷  typed_slice.own_slice sl byteT (DfracOwn 1) data ∗
      "Hs_ptr" ∷ s ↦[slice.T HostName] (slice_val shardMap_sl) ∗
      "HshardMap_sl" ∷ typed_slice.own_slice_small (V:=u64) shardMap_sl HostName (DfracOwn 1) shardMapping
  }}}.
Proof.
  wp_pures. iIntros (Hshards Φ) "H HΦ".
  iNamed "H".
  wp_lam.

  wp_pures.
  wp_apply (wp_new_enc).
  iIntros (enc) "Henc".
  wp_pures.
  change (uint.Z (word.mul 8 65536)) with (8 * 65536).

  wp_load.
  wp_apply (wp_Enc__PutInts with "[$Henc $HshardMap_sl]").
  { rewrite /uNSHARD in Hshards. rewrite Hshards. word. }
  iIntros "[Henc HshardMap_sl]".

  wp_apply (wp_Enc__Finish with "Henc").
  iIntros (rep_sl repData).
  iIntros "(%Henc & %Hlen & Hrep_sl)".
  iApply "HΦ". rewrite /named. iFrame. iPureIntro.
  rewrite /has_encoding_shardMapping. done.
Qed.

Lemma wp_KVCoord__AddServerRPC s x γ γsh :
  {{{ "#His_memkv" ∷ is_KVCoordServer s γ ∗
      "#His_shard" ∷ is_shard_server x γsh ∗
      "%Heq_kv_gn" ∷ ⌜γsh.(kv_gn) = γ.(coord_kv_gn)⌝
  }}}
    KVCoord__AddServerRPC #s #x
  {{{ RET #(); True%I }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_pures.
  iNamed "His_memkv".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapInsert with "[$]").
  { eauto. }
  iIntros "Hmap".
  wp_pures.
  wp_loadField.
  wp_apply (wp_MapLen with "[$Hmap]").
  remember (size (typed_map.map_insert hostShards x 0)) as num_shards eqn:Heq_num_shards.
  iIntros "(%Hmap_size&Hmap)".
  wp_pures.
  wp_apply (wp_ref_of_zero _ _ (uint64T)).
  { econstructor. }
  iIntros (nf_left_ptr) "Hnf_left".
  wp_pures.
  wp_apply (wp_StoreAt with "[$]").
  { naive_solver. }
  iIntros "Hnf_left".
  wp_pures.
  wp_loadField.
  iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "(HshardMap_sl&HshardMap_clo)".
  wp_bind (forSlice _ _ _).
  rewrite /forSlice.
  wp_pures.
  wp_apply (wp_slice_len).
  (* wp_pures would reduce too far *)
  wp_pure (goose_lang.Rec _ _ _).
  wp_pure (goose_lang.App _ _).
  wp_pure (goose_lang.Rec _ _ _).

  (* We want to generalize over the loop argument, which is 0, but there are many occurrences of 0.
     This is a hack to only eplace that one occurence. *)
  pose (k' := W64 0).
  assert (k' = 0) as Heqk by auto.
  iEval (rewrite -{-1}Heqk).
  clear Heqk. remember k' as k eqn:Heqk. clear Heqk.

  remember ((word.sub num_shards (word.sub 65536
                                          (word.divu (word.mul num_shards 65536) num_shards))))
           as nf_left eqn:Hnf_left.
  clear Hnf_left.

  remember ((typed_map.map_insert hostShards x 0)) as hostShards'.
  clear HeqhostShards'.
  clear Heq_num_shards.
  iLöb as "IH" forall (k hostShards' nf_left shardMapping Hlen_shardMapping HshardMapping_dom) "HshardServers".
  wp_pures.
  iFreeze "IH".
  wp_if_destruct; last first.
  { iClear "IH". wp_pures. wp_loadField. wp_apply (release_spec with "[-HΦ]").
    { iFrame "Hlocked HmuInv". iNext. iExists _, _, _, _, _.
      iDestruct ("HshardMap_clo" with "[$]") as "$".
      iFrame. iSplit; eauto. }
    wp_pures. iApply "HΦ". eauto. }
  iDestruct (typed_slice.own_slice_small_sz (V:=u64) with "[$]") as %Hsz.
  edestruct (list_lookup_lt _ (shardMapping) (uint.nat k)) as (v&Heq).
  { word_cleanup. }
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[HshardMap_sl]").
  { rewrite /HostName. iFrame "HshardMap_sl". iPureIntro. eauto. }
  iIntros "HshardMap_sl". wp_pures.
  wp_loadField. wp_apply (wp_MapGet with "[$]").
  iIntros (v' ok) "(%Hget&Hmap)".
  wp_pures.
  wp_if_destruct; last first.
  { wp_pure (goose_lang.Rec _ _ _).
    wp_pure (goose_lang.App _ _).
    iThaw "IH".
    wp_pure (_ + _)%E.
    iApply ("IH" $! _ with "[//] [//] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  }
  wp_pures.
  wp_if_destruct.
  {
    wp_apply (wp_LoadAt with "[$]").
    iIntros "Hnf_left_ptr". wp_pures.
    wp_if_destruct.
    {
      wp_apply (wp_LoadAt with "[$]").
      iIntros "Hnf_left_ptr". wp_pures.
      wp_apply (wp_StoreAt with "[$]").
      { naive_solver. }
      iIntros "Hnf_left_ptr". wp_pures.
      wp_loadField.
      rewrite /all_are_shard_servers.
      iDestruct ("HshardServers" $! _ _ with "[//]") as (γh) "(His_shard_host&Heq)".
      wp_apply (wp_ShardClerkSet__GetClerk with "[$]").
      iIntros (ck_ptr) "(Hclerk&Hclerk_clo)".
      wp_bind (KVShardClerk__MoveShard #ck_ptr #_ #x).
      wp_apply (wp_KVShardClerk__MoveShard with "[$Hclerk]").
      { iFrame "His_shard". iPureIntro.
        eapply lookup_lt_Some in Heq. lia. }
      iIntros "Hclerk".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapInsert with "[$]").
      { naive_solver. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapGet with "[$]").
      iIntros (v' ok') "(%Hget'&Hmap)".
      wp_pures. wp_loadField.
      wp_apply (wp_MapInsert with "[$]").
      { naive_solver. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (typed_slice.wp_SliceSet (V:=u64) with "[$HshardMap_sl]").
      { eauto. }
      iIntros "HshardMap_sl".
      wp_pure (goose_lang.Rec _ _ _).
      wp_pure (goose_lang.App _ _).
      iThaw "IH".
      wp_pure (_ + _)%E.
      iDestruct ("Hclerk_clo" with "[$]") as "Hclerk".
      iApply ("IH" $! _ (typed_map.map_insert
                  (typed_map.map_insert hostShards' v (word.sub (word.add (word.divu 65536 _) 1) 1))
                  x (word.add v' 1)) with "[] [] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
      { iPureIntro. rewrite insert_length. eauto. }
      { iPureIntro. intros i Hlt.
        destruct (decide (i = k)).
        { subst. rewrite list_lookup_insert; eauto.
          word. }
        { rewrite list_lookup_insert_ne; eauto.
          intros Heq'.
          apply Z2Nat.inj in Heq'; try word.
          eapply (int_Z_inj) in Heq'; eauto. apply _.
        }
      }
      iModIntro. iIntros (? Hin Hlookup').
      destruct (decide (sid = uint.nat k)).
      {
        subst. rewrite list_lookup_insert in Hlookup'; last by word.
        iExists _. inversion Hlookup'; subst. iFrame "His_shard".
        eauto.
      }
      iClear "IH".
      rewrite list_lookup_insert_ne in Hlookup'; last by word.
      iApply "HshardServers"; eauto.
    }
    wp_pure (goose_lang.Rec _ _ _).
    wp_pure (goose_lang.App _ _).
    wp_pure (_ + _)%E.
    iThaw "IH".
    iApply ("IH" $! _ _ with "[//] [//] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  }
  {
    wp_loadField.
      rewrite /all_are_shard_servers.
      iDestruct ("HshardServers" $! _ _ with "[//]") as (γh) "(His_shard_host&Heq)".
      wp_apply (wp_ShardClerkSet__GetClerk with "[$]").
      iIntros (ck_ptr) "(Hclerk&Hclerk_clo)".
      wp_bind (KVShardClerk__MoveShard #ck_ptr #_ #x).
      wp_apply (wp_KVShardClerk__MoveShard with "[$Hclerk]").
      { iFrame "His_shard". iPureIntro.
        eapply lookup_lt_Some in Heq. lia. }
      iIntros "Hclerk".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapInsert with "[$]").
      { naive_solver. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (wp_MapGet with "[$]").
      iIntros (v'' ok'') "(%Hget'&Hmap)".
      wp_pures. wp_loadField.
      wp_apply (wp_MapInsert with "[$]").
      { naive_solver. }
      iIntros "Hmap".
      wp_pures.
      wp_loadField.
      wp_apply (typed_slice.wp_SliceSet (V:=u64) with "[$HshardMap_sl]").
      { eauto. }
      iIntros "HshardMap_sl".
      wp_pure (goose_lang.Rec _ _ _).
      wp_pure (goose_lang.App _ _).
      iThaw "IH".
      wp_pure (_ + _)%E.
      iDestruct ("Hclerk_clo" with "[$]") as "Hclerk".
      iApply ("IH" $! _ _ with "[] [] [$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
      { iPureIntro. rewrite insert_length. eauto. }
      { iPureIntro. intros i Hlt.
        destruct (decide (i = k)).
        { subst. rewrite list_lookup_insert; eauto.
          word. }
        { rewrite list_lookup_insert_ne; eauto.
          intros Heq'.
          apply Z2Nat.inj in Heq'; try word.
          eapply (int_Z_inj) in Heq'; eauto. apply _.
        }
      }
      iModIntro. iIntros (? Hin Hlookup').
      destruct (decide (sid = uint.nat k)).
      {
        subst. rewrite list_lookup_insert in Hlookup'; last by word.
        iExists _. inversion Hlookup'; subst. iFrame "His_shard".
        eauto.
      }
      iClear "IH".
      rewrite list_lookup_insert_ne in Hlookup'; last by word.
      iApply "HshardServers"; eauto.
    }
Qed.

Lemma wp_KVCoordServer__Start (s:loc) (host : u64) γ :
is_urpc_dom γ.(coord_urpc_gn) {[ W64 1; W64 2 ]} -∗
is_coord_server host γ -∗
is_KVCoordServer s γ -∗
  {{{
       True
  }}}
    KVCoord__Start #s #host
  {{{
       RET #(); True
  }}}.
Proof.
  iIntros "#Hdom #His_coord #His_memkv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  wp_apply (map.wp_NewMap u64).
  iIntros (handlers_ptr) "Hmap".
  wp_pures.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.
  rewrite /KVCoord__GetShardMapRPC.

  wp_apply (map.wp_MapInsert with "Hmap").
  iIntros "Hmap".
  wp_pures.

  wp_apply (wp_MakeServer with "[$Hmap]").
  iIntros (rs) "Hsown".
  wp_pures.

  iNamed "His_coord".
  wp_apply (wp_StartServer with "[$Hsown]").
  { rewrite ?dom_insert_L; set_solver. }
  {
    iSplitL "".
    { rewrite /handlers_complete.
      rewrite ?dom_insert_L dom_empty_L. iExactEq "Hdom". f_equal. set_solver. }
    iApply (big_sepM_insert_2 with "").
    { (* GetShardMapping RPC handler_is *)
      iExists _.
      iFrame "HgetSpec".

      clear Φ.
      iIntros (????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hpre)".
      simpl.
      iNamed "His_memkv".
      wp_loadField.
      wp_apply (acquire_spec with "[$HmuInv]").
      iIntros "[Hlocked Hown]".
      iNamed "Hown".
      wp_pures.
      wp_apply (wp_struct_fieldRef_pointsto with "[$shardMap]").
      { eauto. }
      iIntros (fl) "(H1&H2)".
      iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_close]".
      wp_apply (wp_encodeShardMap with "[$]").
      { word_cleanup. rewrite wrap_small; last (rewrite /uNSHARD; lia).
        rewrite -Hlen_shardMapping. lia. }
      iIntros (sl data) "(%Henc&H)".
      wp_apply (wp_StoreAt with "[$]").
      { apply slice_val_ty. }
      iIntros "Hrep".
      iNamed "H".
      iDestruct ("HshardMap_close" with "HshardMap_sl") as "HshardMap_sl".
      iDestruct (own_slice_to_small with "Hdata") as "Hdata".
      wp_pures.
      wp_loadField.
      wp_apply (release_spec with "[-HΦ Hrep Hdata]").
      { iFrame "Hlocked HmuInv".
        iNext. iExists _, _, _, _, _. iFrame. iFrame "#". iFrame "%".
        iDestruct "H1" as %Hequiv. iApply Hequiv. iFrame. }
      wp_pures. iApply "HΦ". iFrame. iModIntro. iExists _. iFrame "% #".
    }
    iApply (big_sepM_insert_2 with "").
    { (* AddServerRPC *)
      iExists _.
      iFrame "HaddSpec".

      clear Φ.
      rewrite /is_urpc_handler.
      iIntros (????) "!#".
      iIntros (Φ) "Hpre HΦ".
      wp_pures.
      iDestruct "Hpre" as "(Hreq_sl & Hrep & Hpre)".
      simpl.
      iDestruct "Hpre" as "(%Henc&Hshard)".
      iDestruct "Hshard" as (γsh Heq) "#His_shard".
      wp_apply (wp_DecodeUint64' with "[$Hreq_sl]"); first by eauto.
      wp_pures.
      simpl in x.
      wp_apply (wp_KVCoord__AddServerRPC with "[]").
      { iSplitL "".
        { rewrite /named. iExactEq "His_memkv". eauto. }
        iFrame "His_shard". eauto.
      }
      wp_pures. iModIntro. iApply "HΦ". iFrame.
      iDestruct (own_slice_zero byteT (DfracOwn 1)) as "Hnil".
      rewrite own_slice_to_small. iFrame "Hnil".
    }
    rewrite big_sepM_empty. eauto.
  }
  wp_pures. iApply "HΦ".
  auto.
Qed.

End memkv_coord_start_proof.
