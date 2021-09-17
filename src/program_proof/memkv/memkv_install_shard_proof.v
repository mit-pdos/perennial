From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_install_shard_proof.

Section memkv_install_shard_proof.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_InstallShardRPC (s args_ptr:loc) args γ γreq :
  is_KVShardServer s γ -∗
  {{{
       own_InstallShardRequest args_ptr args ∗
       ⌜int.nat args.(IR_Sid) < uNSHARD⌝ ∗
       is_RPCRequest γ.(rpc_gn) γreq (own_shard γ.(kv_gn) args.(IR_Sid) args.(IR_Kvs))
                                (λ _, True)
                                {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
  }}}
    KVShardServer__InstallShardRPC #s #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & %HsidLe & #HreqInv)".
  iNamed "Hargs".
  wp_lam.
  wp_pures.
  iNamed "His_shard".
  wp_loadField.
  wp_apply (acquire_spec with "HmuInv").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_lam.
  wp_pures.

  wp_loadField. wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "[%HseqGet HlastSeqMap]".
  wp_pures.

  wp_loadField. wp_pures.
  wp_apply (wp_and ok (int.Z args.(IR_Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }

  wp_if_destruct.
  { (* reply table *)
    wp_pures.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_,_,_,_,_,_.
      iExists _,_,_,_.
      iFrame "HlastReply_structs ∗".
      done.
    }
    wp_pures. by iApply "HΦ".
  }

  (* fresh sequence number *)
  assert (int.Z v < int.Z args.(IR_Seq))%Z as HseqFresh.
  {
    simpl.
    destruct ok.
    {
      intuition.
      destruct (Z.le_gt_cases (int.Z args.(IR_Seq)) (int.Z v)) as [Hineq|Hineq].
      { naive_solver. }
      { naive_solver. }
    }
    {
      apply map_get_false in HseqGet as [_ ->].
      simpl.
      word.
    }
  }

  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_MapInsert with "HlastSeqMap").
  { done. }
  iIntros "HlastSeqMap".

  (* update shardMap to have sid ↦ true *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[HshardMap_small HshardMap_sl]".
  wp_apply (typed_slice.wp_SliceSet with "[$HshardMap_small]").
  {
    iPureIntro.
    apply lookup_lt_is_Some_2.
    move: HshardMapLength.
    word.
  }
  iIntros "HshardMap_small".
  iSpecialize ("HshardMap_sl" with "HshardMap_small").

  (* install shard *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iDestruct (slice.is_slice_split with "Hkvss_sl") as "[Hkvss_small Hkvss_sl]".
  wp_apply (slice.wp_SliceSet with "[$Hkvss_small]").
  {
    iPureIntro.
    split.
    {
      simpl.
      rewrite list_lookup_fmap.
      rewrite fmap_is_Some.
      apply lookup_lt_is_Some_2.
      word.
    }
    {
      naive_solver.
    }
  }
  iIntros "Hkvss_small".
  iCombine "Hkvss_sl Hkvss_small" as "Hkvss_sl".

  iMod (server_takes_request with "HreqInv Hrpc") as "HH".
  { done. }
  {
    rewrite HseqGet.
    simpl.
    word.
  }
  iDestruct "HH" as "(Hγpre & HownShard & Hproc)".
  iMod (server_completes_request _ _ _ _ _ (mkShardReplyC 0 [] false) with "His_srv HreqInv Hγpre [] Hproc") as "HH".
  { done. }
  { done. }
  { rewrite HseqGet. simpl. word. }
  { done. }
  iDestruct "HH" as "[#Hreceipt Hrpc]".

  wp_pures.
  wp_loadField.
  wp_loadField.

  wp_apply (map.wp_MapInsert with "HlastReplyMap").
  iIntros "HlastReplyMap".
  wp_pures.

  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_,_,_.
    iExists _,_,_,_.
    iFrame "HlastReplyMap HlastSeqMap".
    iFrame.
    iSplitL "".
    {
      iPureIntro. rewrite dom_insert_L.
      rewrite dom_insert_L. rewrite HlastReplyMVdom.
      done.
    }
    iSplitL "HlastReply_structs".
    { (* added an empty reply to lastReply *)
      iApply (big_sepM2_insert_2 with "[] HlastReply_structs").
      simpl.
      iExists (Slice.nil),1%Qp.
      iSplitL ""; first done.
      iApply typed_slice.is_slice_small_nil.
      done.
    }
    iSplitL "Hkvss_sl".
    {
      iDestruct "Hkvss_sl" as "[$ H]".
      rewrite -list_fmap_insert.
      iFrame.
    }
    iSplitL "".
    { iPureIntro. by rewrite insert_length. }
    iSplitL "".
    { iPureIntro. by rewrite insert_length. }

    iApply (big_sepS_wand with "HownShards").
    iApply (big_sepS_delete _ _ (args.(IR_Sid))).
    { set_solver. }
    iSplitR "".
    {
      iIntros "_".
      iRight.
      iExists _,_,_.
      iFrame.
      iPureIntro.
      split.
      - apply list_lookup_insert.
        move: HkvssLength. word.
      - eauto.
    }
    iApply big_sepS_intro.
    iModIntro.
    iIntros.
    assert (x ≠ args.(IR_Sid)).
    { set_solver. }
    assert (int.nat x ≠ int.nat args.(IR_Sid)).
    {
      destruct (bool_decide (int.Z x = int.Z args.(IR_Sid))) as [|] eqn:X.
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

End memkv_install_shard_proof.
