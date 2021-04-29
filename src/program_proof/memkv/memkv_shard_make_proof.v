From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_put_proof memkv_conditional_put_proof memkv_get_proof memkv_install_shard_proof memkv_getcid_proof memkv_move_shard_proof common_proof.

Section memkv_shard_make_proof.

Context `{!heapG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_MakeMemKVShardServer (b : bool) γ :
  {{{
       True
  }}}
    MakeMemKVShardServer #b
  {{{
       s, RET #s; is_MemKVShardServer s γ
  }}}.
Proof.
  iIntros (Φ) "? HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.  Opaque slice.T. }
  iIntros (srv) "srv".
  wp_pures.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  iDestruct (struct_fields_split with "srv") as "srv". iNamed "srv".
  wp_storeField.
  replace  (ref (InjLV (#0, (zero_val (slice.T byteT), (#false, #())))))%E
    with (NewMap (struct.t ShardReply)) by naive_solver.
  wp_apply (map.wp_NewMap).
  iIntros (lastReply_ptr) "HlastReplyMap".
  wp_storeField.
  replace (ref (InjLV #0))%E with (NewMap uint64T) by naive_solver.
  wp_apply (wp_NewMap).
  iIntros (lastSeq_ptr) "HlastSeqMap".
  wp_storeField.
  wp_apply (typed_slice.wp_NewSlice).
  iIntros (shardMap_sl) "HshardMap_sl".
  Transparent slice.T. wp_storeField. Opaque slice.T.
  wp_apply (wp_new_slice).
  { econstructor. }
  iIntros (kvss_sl) "Hkvss_sl".
  Transparent slice.T. wp_storeField. Opaque slice.T.
  replace (ref (InjLV #null))%E with ((NewMap (struct.ptrT MemKVShardClerk))) by auto.
  wp_apply (wp_NewMap).
  iIntros (peers_ptr) "HpeersMap".
  wp_storeField.
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (iptr) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i,
      "shardMap" ∷ srv ↦[MemKVShardServer :: "shardMap"] (slice_val shardMap_sl) ∗
      "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl boolT 1
                                            (replicate (int.nat i) b ++
                                             replicate (int.nat (U64 65536) - int.nat i) IntoVal_def))%I
          with "[] [$Hi HshardMap_sl shardMap]").
  { word. }
  { iIntros (i Φ') "!# H HΦ".
    iDestruct "H" as "(H1&H2)".
    iNamed "H1".
    iDestruct "H2" as "(Hi&%Hbound)".
    wp_pures.
    wp_apply (wp_LoadAt with "[$Hi]").
    iIntros "Hi".
    wp_loadField.
    simpl in Hbound.
    admit.
  }
  { iFrame "shardMap".
    change (int.nat 0) with 0%nat.
    rewrite replicate_0 app_nil_l.
    iFrame "HshardMap_sl". }
  iIntros "(H&Hi)". iNamed "H".
  wp_pures.
Abort.

End memkv_shard_make_proof.
