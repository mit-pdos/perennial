From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_proof memkv_marshal_install_shard_proof.

Section memkv_install_shard_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC}.

Lemma wp_InstallShardRPC (s args_ptr:loc) args γ γreq :
  is_MemKVShardServer s γ -∗
  {{{
       own_InstallShardRequest args_ptr args ∗
       is_RPCRequest γ.(rpc_gn) γreq (own_shard γ.(kv_gn) args.(IR_Sid) args.(IR_Kvs))
                                (λ _, True)
                                {| Req_CID:=args.(IR_CID); Req_Seq:=args.(IR_Seq) |}
  }}}
    MemKVShardServer__InstallShardRPC #s #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "[Hargs #HreqInv]".
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

  wp_apply (wp_and ok (int.Z args.(IR_Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". admit. (* tweak code to make less annoying *) }

  wp_if_destruct.
  { (* reply table *)
    admit.
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
    admit. (* TODO: same as something done before *)
  }
  iIntros "HshardMap_small".
  iSpecialize ("HshardMap_sl" with "HshardMap_small").

  (* install shard *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iDestruct (is_slice_split with "Hkvss_sl") as "[Hkvss_small Hkvss_sl]".
  wp_apply (wp_SliceSet with "[$Hkvss_small]").
  {
    (* FIXME: keep track of length of kvss_sl *)
    admit.
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
  iMod (server_completes_request with "His_srv HreqInv Hγpre [] Hproc") as "HH".
  { done. }
  { done. }
  { rewrite HseqGet. simpl. word. }
  { done. }
  iDestruct "HH" as "[#Hreceipt Hrpc]".

  wp_pures.
  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_,_,_.
    iExists _,_,_.
    iFrame "HlastReplyMap HlastSeqMap HlastReply_structs".
    iFrame.
    iSplitL ""; first admit. (* TODO: either update code, or change proof to account for the fact that lastReplyM and lastSeqM don't stay in sync *)
    iSplitL "Hkvss_sl".
    {
      iDestruct "Hkvss_sl" as "[$ H]".
      rewrite -list_fmap_insert.
      iFrame.
    }
    iSplitL "Hrpc".
    { admit. }
    iSplitL "".
    {
      iPureIntro. by rewrite insert_length.
    }

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
      apply list_lookup_insert.
      admit. (* FIXME: keep track of the length of kvs_ptrs, and keep bound on IR_Sid to know that it isn't too big *)
    }
    iApply big_sepS_intuitionistically_forall.
    iModIntro.
    iIntros.
    assert (x ≠ args.(IR_Sid)).
    { set_solver. }
    assert (int.nat x ≠ int.nat args.(IR_Sid)).
    { admit. } (* TODO: use injectivity of u64 -> nat mapping *)
    rewrite list_lookup_insert_ne; last done.
    rewrite list_lookup_insert_ne; last done.
    iFrame.
  }
  by iApply "HΦ".
Admitted.

End memkv_install_shard_proof.
