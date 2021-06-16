From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_getcid_proof memkv_shard_clerk_proof.

Section memkv_getcid_proof.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_GetCIDRPC (s:loc) γ :
  is_MemKVShardServer s γ -∗
  {{{
       True
  }}}
    MemKVShardServer__GetCIDRPC #s
  {{{
       cid, RET #cid; RPCClient_own_ghost γ.(rpc_gn) cid 1
  }}}
.
Proof.
  iIntros "#Hmemkv !#" (Φ) "_ HΦ".
  wp_lam.
  iNamed "Hmemkv".
  wp_loadField.
  wp_apply (acquire_spec with "[$HmuInv]").
  iIntros "[Hlocked Hown]".
  iNamed "Hown".
  wp_pures.
  wp_loadField.
  wp_pures.
  wp_loadField.
  wp_apply wp_SumAssumeNoOverflow.
  iIntros (Hoverflow).

  wp_loadField.
  wp_storeField.
  iDestruct (big_sepS_delete _ _ nextCID with "Hcids") as "[Hcid Hcids]".
  { set_solver. }

  wp_loadField.
  wp_apply (release_spec with "[-HΦ Hcid]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_,_,_.
    iExists _,_,_,_.
    iFrame "HlastReply_structs ∗".
    iSplitL ""; first done.
    iSplitL ""; first done.
    iSplitL ""; first done.
    iApply (big_sepS_delete _ _ nextCID with "[Hcids]").
    { set_solver. }
    iSplitL "".
    {
      iLeft.
      iPureIntro.
      word.
    }
    iApply (big_sepS_impl with "Hcids").
    iModIntro. iIntros (??) "[%Hineq|$]".
    iLeft. iPureIntro.
    word.
  }
  wp_pures.
  iApply "HΦ".
  iModIntro.
  iDestruct "Hcid" as "[%Hbad|$]".
  exfalso.
  word.
Qed.

End memkv_getcid_proof.
