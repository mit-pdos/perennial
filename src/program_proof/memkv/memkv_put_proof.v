From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

#[local] Set Universe Polymorphism.

Section memkv_put_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_PutRPC (s args_ptr reply_ptr:loc) val_sl args γ Q :
  is_KVShardServer s γ -∗
  {{{
       own_PutRequest args_ptr val_sl args ∗
       (∃ dummy_rep, own_PutReply reply_ptr dummy_rep) ∗
       (PreShardPut γ.(kv_gn) args.(PR_Key) Q args.(PR_Value))
  }}}
    KVShardServer__PutRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_PutReply reply_ptr rep ∗
       (PostShardPut γ.(kv_gn) args.(PR_Key) Q args.(PR_Value)) rep
  }}}.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & Hrep & Hpre)".
  iNamed "Hargs". iNamed "Hrep".

  wp_lam.
  wp_pures.

  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".

  iNamed "Hown".

  wp_pures.
  wp_lam.
  wp_pures.

  wp_pures.
  wp_loadField.
  wp_apply (wp_shardOf).
  wp_pures.
  wp_loadField.

  iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
  set (sid:=shardOfC args.(PR_Key)) in *.

  assert (∃ b, shardMapping !! uint.nat sid = Some b) as [? ?].
  {
    eapply list_lookup_lt.
    move: HshardMapLength. rewrite /sid /shardOfC /uNSHARD.
    word.
  }
  wp_apply (typed_slice.wp_SliceGet with "[$HshardMap_sl]").
  {
    iPureIntro. done.
  }
  iIntros "HshardMap_sl".
  wp_pures.

  wp_if_destruct.
  { (* have the shard *)
    wp_loadField.
    wp_loadField.
    wp_loadField.
    iDestruct (slice.own_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
    iDestruct (big_sepS_elem_of_acc _ _ sid with "HownShards") as "[HownShard HownShards]".
    { set_solver. }
    iDestruct "HownShard" as "[%Hbad|HownShard]".
    { exfalso. done. }
    iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & %Hdom_kvs & HkvsMap & HvalSlices)".
    wp_apply (slice.wp_SliceGet _ _ _ _ _ _ _ (#kvs_ptr) with "[Hkvss_sl]").
    {
      iFrame "Hkvss_sl".
      iPureIntro.
      rewrite list_lookup_fmap.
      rewrite Hkvs_lookup.
      done.
    }
    iIntros "[Hkvss_sl %Hkvs_ty]".

    wp_apply (map.wp_MapInsert with "[$HkvsMap]").
    iIntros "HkvsMap".
    wp_pures.
    wp_storeField.
    iDestruct (big_sepS_delete _ _ args.(PR_Key) with "HshardGhost") as "[Hghost HshardGhost]".
    { set_solver. }
    iDestruct "Hghost" as "[%Hbad|Hkvptsto]".
    { exfalso; done. }

    (* Get Q by using fupd *)
    unfold PreShardPut.
    iApply fupd_wp.
    iMod "Hpre".
    iDestruct "Hpre" as (v0) "(Hkvptsto2 & HfupdQ)".
    iMod (kvptsto_update args.(PR_Value) with "Hkvptsto Hkvptsto2") as "[Hkvptsto Hkvptsto2]".
    iMod ("HfupdQ" with "Hkvptsto") as "Q".
    iModIntro.


    iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
    wp_loadField.
    wp_apply (release_spec with "[> -HΦ Q HKey Hrep]").
    {
      iFrame "HmuInv Hlocked".
      iModIntro. iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      iSplitL ""; first done.
      iSplitL ""; first done.
      iApply "HownShards".
      iRight.
      iExists _, _, _.
      iFrame.
      instantiate (1:=(<[args.(PR_Key):=args.(PR_Value)]> m)).
      iSplitL "HshardGhost Hkvptsto2".
      {
        iApply (big_sepS_delete _ _ args.(PR_Key) with "[-]").
        { set_solver. }
        iSplitL "Hkvptsto2".
        {
          iRight.
          rewrite lookup_insert.
          iFrame.
        }
        iApply (big_sepS_impl with "HshardGhost").
        iModIntro; iIntros.
        rewrite lookup_insert_ne; last first.
        { set_solver. }
        iFrame.
      }
      iSplitL ""; first done.
      iSplitL "".
      { rewrite ?dom_insert_L //; eauto. iPureIntro; congruence. }
      iApply (big_sepS_delete _ _ args.(PR_Key) with "[-]").
      { set_solver. }
      iSplitL "".
      {
        simpl. iRight.
        iExists val_sl.
        rewrite lookup_insert.
        rewrite lookup_insert.
        by iFrame "∗#".
      }
      iDestruct (big_sepS_delete _ _ args.(PR_Key) with "HvalSlices") as "[_ HvalSlices]".
      { set_solver. }
      iApply (big_sepS_impl with "HvalSlices").
      iModIntro.
      iIntros.
      rewrite lookup_insert_ne; last first.
      { set_solver. }
      rewrite lookup_insert_ne; last first.
      { set_solver. }
      iFrame "∗#".
    }
    wp_pures. iModIntro. iApply "HΦ".
    iSplitL "Hrep".
    {
      instantiate (1:=mkPutReplyC _).
      iFrame.
    }
    iRight.
    iSimpl.
    by iFrame.
  }
  { (* don't have shard *)
    wp_storeField.

    wp_loadField.
    iSpecialize ("HshardMap_sl_close" with "HshardMap_sl").
    wp_apply (release_spec with "[-HΦ Hpre HKey Hrep]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      done.
    }
    wp_pures. iModIntro. iApply "HΦ".
    iSplitL "Hrep".
    {
      instantiate (1:=mkPutReplyC _).
      iFrame.
    }
    iLeft.
    iSimpl.
    by iFrame.
  }
Qed.

End memkv_put_proof.

Ltac Zify.zify_post_hook ::= idtac.
