From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_move_shard_proof memkv_shard_clerk_proof.

#[local] Set Universe Polymorphism.

Section memkv_move_shard_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_MoveShardRPC (s args_ptr:loc) args γsh γ :
  is_KVShardServer s γ -∗
  {{{
       own_MoveShardRequest args_ptr args ∗
       ⌜uint.Z args.(MR_Sid) < uNSHARD⌝ ∗
       is_shard_server args.(MR_Dst) γsh ∗
       ⌜ γsh.(kv_gn) = γ.(kv_gn) ⌝
  }}}
    KVShardServer__MoveShardRPC #s #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & %HsidLe & #Hother_shard & %Heq_kv_gn)".
  wp_lam.
  wp_pures.
  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_pures.

  iNamed "Hargs".
  wp_loadField. wp_loadField.
  (* initialize peer if necessary *)
  wp_apply (wp_MapGet with "HpeersMap").
  iIntros (v ok) "[%Hlookup HpeersMap]".
  wp_pures.
  wp_apply (wp_If_join_evar' (∃ peersM, "%Hlookup'" ∷ ⌜ is_Some (peersM !! args.(MR_Dst)) ⌝ ∗
                        "HDst" ∷ args_ptr ↦[MoveShardRequest :: "Dst"] #args.(MR_Dst) ∗
                        "Hpeers" ∷ s ↦[KVShardServer :: "peers"] #peers_ptr ∗
                        "HpeerClerks" ∷ ([∗ map] ck ∈ peersM, own_KVShardClerk ck γ.(kv_gn)) ∗
                        "HpeersMap" ∷ own_map peers_ptr (DfracOwn 1) peersM)%I
              with "[HDst HpeersMap HpeerClerks Hpeers]").
  {
    wp_if_destruct.
    - do 2 wp_loadField.
      wp_apply (wp_MakeFreshKVShardClerk with "Hother_shard Hiscm").
      iIntros (ck) "Hclerk".
      wp_pures. wp_loadField. wp_loadField.
      wp_apply (wp_MapInsert with "[$]").
      { eauto. }
      iIntros "Hmap".
      wp_pures.
      iSplit; eauto.
      iExists _. iFrame "∗#".
      iSplit.
      { iPureIntro. rewrite /typed_map.map_insert lookup_insert; eauto. }
      iApply big_sepM_insert.
      { apply map_get_false in Hlookup; intuition. }
      rewrite Heq_kv_gn. iFrame.
    - iModIntro. iSplit; auto.
      iExists _. iFrame. iPureIntro.
      { apply map_get_true in Hlookup; intuition auto. }
  }
  clear peersM Hlookup.
  iNamed 1.
  iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "[HshardMap_small HshardMap_sl]".

  assert (∃ b, shardMapping !! uint.nat args.(MR_Sid) = Some b) as [? ?].
  {
    eapply list_lookup_lt.
    word.
  }

  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_apply (typed_slice.wp_SliceGet with "[$HshardMap_small]").
  { done. }
  iIntros "HshardMap_small".
  wp_pures.
  wp_if_destruct.
  { (* don't have the shard, so we're not going to install it somewhere else *)
    iSpecialize ("HshardMap_sl" with "HshardMap_small").
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HSid]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      done.
    }
    wp_pures.
    by iApply "HΦ".
  }
  (* have a clerk already in peers *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  iDestruct (slice.own_slice_split with "Hkvss_sl") as "[Hkvss_small Hkvss_sl]".
  iDestruct (big_sepS_delete _ _ args.(MR_Sid) with "HownShards") as "[HownShard HownShards]".
  { set_solver. }
  iDestruct "HownShard" as "[%Hbad|HownShard]".
  { exfalso. done. }
  iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & %Hkvs_dom & HkvsMap & HvalSlices)".

  wp_apply (slice.wp_SliceGet with "[$Hkvss_small]").
  {
    iPureIntro.
    rewrite list_lookup_fmap.
    rewrite Hkvs_lookup.
    done.
  }
  iIntros "[Hkvss_small %Hkvs_ty]".
  wp_pures.

  wp_apply (map.wp_NewMap u64).
  iIntros (empty_ptr) "HemptyMap".
  wp_loadField.
  wp_loadField.

  wp_apply (slice.wp_SliceSet with "[$Hkvss_small]").
  {
    iPureIntro.
    split.
    { rewrite list_lookup_fmap. rewrite Hkvs_lookup. apply fmap_is_Some.
      naive_solver. }
    naive_solver.
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
  destruct Hlookup' as (v'&Hlookup').
  assert (v' = v0) as [].
  { replace v0 with (fst (map_get peersM args.(MR_Dst))); last first.
    { rewrite Hlookup2 //=. }
    rewrite map_get_val Hlookup' //. }
  wp_pures.
  iDestruct (big_sepM_lookup_acc _ _ args.(MR_Dst) with "HpeerClerks") as "[Hclerk HpeerClerks]".
  { eauto. }
  wp_apply (wp_KVShardClerk__InstallShard with "[Hclerk HkvsMap HvalSlices HshardGhost]").
  {
    iFrame "Hclerk".
    iFrame "HshardGhost".
    iSplitR ""; last (iPureIntro; word).
    iExists _; iFrame.
    eauto.
  }
  iIntros "Hclerk".
  iSpecialize ("HpeerClerks" with "[Hclerk]").
  { iFrame. }
  wp_pures.
  wp_loadField.
  iSpecialize ("HshardMap_sl" with "HshardMap_small").
  wp_apply (release_spec with "[- HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_.
    iFrame.
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
      word.
    }
    iApply (big_sepS_impl with "HownShards").
    iModIntro.
    iIntros.

    assert (x ≠ args.(MR_Sid)).
    { set_solver. }
    assert (uint.nat x ≠ uint.nat args.(MR_Sid)).
    {
      destruct (bool_decide (uint.Z x = uint.Z args.(MR_Sid))) as [|] eqn:X.
      {
        apply bool_decide_eq_true in X.
        apply word.unsigned_inj in X.
        done.
      }
      {
        apply bool_decide_eq_false in X.
        word.
      }
    }

    rewrite list_lookup_insert_ne; last done.
    rewrite list_lookup_insert_ne; last done.
    iFrame.
  }
  wp_pures. by iApply "HΦ".
Qed.

End memkv_move_shard_proof.
