From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_move_shard_proof memkv_shard_clerk_proof.

Section memkv_move_shard_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Lemma wp_MoveShardRPC (s args_ptr:loc) args γsh γ :
  is_MemKVShardServer s γ -∗
  {{{
       own_MoveShardRequest args_ptr args ∗
       ⌜int.nat args.(MR_Sid) < uNSHARD⌝ ∗
       is_shard_server args.(MR_Dst) γsh
  }}}
    MemKVShardServer__MoveShardRPC #s #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & %HsidLe & #Hother_shard)".
  iNamed "Hargs".
  wp_lam.
  wp_pures.
  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_pures.

  wp_loadField. wp_loadField.
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[HshardMap_small HshardMap_sl]".

  assert (∃ b, shardMapping !! int.nat args.(MR_Sid) = Some b) as [? ?].
  {
    eapply list_lookup_lt.
    rewrite HshardMapLength.
    rewrite /shardOfC /uNSHARD.
    admit. (* TODO: More mod inequality reasoning *)
  }
  wp_apply (typed_slice.wp_SliceGet with "[$HshardMap_small]").
  { done. }
  iIntros "HshardMap_small".
  wp_pures.
  wp_if_destruct.
  { (* don't have the shard, so we're not going to install it somewhere else *)
    iSpecialize ("HshardMap_sl" with "HshardMap_small").
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HCID HSeq HSid]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _, _, _.
      iExists _, _, _, _.
      iFrame "HlastReply_structs".
      iFrame.
      done.
    }
    wp_pures.
    by iApply "HΦ".
  }
  (* have the shard, so we install to the destination *)
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HpeersMap").
  iIntros (v ok) "[%Hlookup HpeersMap]".
  wp_pures.
  wp_if_destruct.
  { (* need to make a fresh clerk *)
    (* FIXME: can't let go of lock here; bug in code *)
    admit.
  }
  (* have a clerk already in peers *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  iDestruct (is_slice_split with "Hkvss_sl") as "[Hkvss_small Hkvss_sl]".
  iDestruct (big_sepS_delete _ _ args.(MR_Sid) with "HownShards") as "[HownShard HownShards]".
  { set_solver. }
  iDestruct "HownShard" as "[%Hbad|HownShard]".
  { exfalso. done. }
  iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & HkvsMap & HvalSlices)".

  wp_apply (wp_SliceGet with "[$Hkvss_small]").
  {
    iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hkvs_lookup.
    done.
  }
  iIntros "[Hkvss_small %Hkvs_ty]".
  wp_pures.

  wp_apply (map.wp_NewMap).
  iIntros (empty_ptr) "HemptyMap".
  wp_loadField.
  wp_loadField.

  wp_apply (wp_SliceSet with "[$Hkvss_small]").
  {
    iPureIntro.
    split.
    { rewrite list_lookup_fmap. rewrite Hkvs_lookup. apply fmap_is_Some.
      naive_solver. }
    admit.
    (* FIXME: goose translated the nil as slice.nil, but we want a nil map *)
  }
  iIntros "Hkvss_small".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (typed_slice.wp_SliceSet with "[$HshardMap_small]").
  {
    iPureIntro.
    eexists _; done.
  }
  iIntros "HshardMap_small".
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapGet with "HpeersMap").
  iIntros (??) "[%Hlookup2 HpeersMap]".
  rewrite Hlookup in Hlookup2.
  assert (v = v0) as [].
  { naive_solver. }
  wp_pures.
  iDestruct (big_sepM_lookup_acc _ _ args.(MR_Dst) with "HpeerClerks") as "[Hclerk HpeerClerks]".
  { apply map_get_true in Hlookup. done. }
  iNamed "Hclerk".
  iDestruct "Hclerk" as "[Hclerk %Hγeq]".
  wp_apply (wp_MemKVShardClerk__InstallShard γsh0 with "[Hclerk HkvsMap HvalSlices HshardGhost]").
  {
    iFrame "Hclerk".
    rewrite Hγeq.
    iFrame "HshardGhost".
    iSplitR ""; last done.
    iExists _; iFrame.
  }
  iIntros "Hclerk".
  iSpecialize ("HpeerClerks" with "[Hclerk]").
  { iExists _; iFrame. done. }
  wp_pures.
  wp_loadField.
  iSpecialize ("HshardMap_sl" with "HshardMap_small").
  wp_apply (release_spec with "[- HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_,_,_.
    iExists _,_,_,_.
    iFrame "HlastReply_structs".
    iFrame.
    iSplitL ""; first done.
    iSplitL "Hkvss_small".
    {
      rewrite -list_fmap_insert.
      iFrame.
    }
    iSplitL "".
    { by rewrite insert_length. }
    iSplitL "".
    { by rewrite insert_length. }
    iApply (big_sepS_delete _ _ (args.(MR_Sid)) with "[HownShards]").
    { set_solver. }
    iSplitL "".
    {
      iLeft.
      iPureIntro.
      rewrite list_lookup_insert.
      { done. }
      rewrite HshardMapLength.
      done.
    }
    iApply (big_sepS_impl with "HownShards").
    iModIntro.
    iIntros.
    rewrite list_lookup_insert_ne; last first.
    { admit. (* TODO: injectivity of int.nat *) }
    rewrite list_lookup_insert_ne; last first.
    { admit. (* TODO: injectivity of int.nat *) }
    iFrame.
  }
  by iApply "HΦ".
Admitted.

End memkv_move_shard_proof.
