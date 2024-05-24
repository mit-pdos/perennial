From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

#[local] Set Universe Polymorphism.

Section memkv_shard_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_shardOf key :
  {{{
       True
  }}}
    shardOf #key
  {{{
       RET #(shardOfC key); True
  }}}.
Proof.
  iIntros (?) "_ HΦ".
  wp_lam.
  wp_pures.
  by iApply "HΦ".
Qed.

Lemma own_shard_agree key v γkv sid m:
  shardOfC key = sid →
  own_shard (Σ:=Σ) γkv sid m -∗ kvptsto γkv key v -∗
  ⌜v = default [] (m !! key)⌝
.
Proof.
  iIntros (?) "Hown Hptsto".
  unfold own_shard.
  iDestruct (big_sepS_elem_of_acc _ _ key with "Hown") as "[[%Hbad|Hown] _]".
  { set_solver. }
  { exfalso. done. }
  iApply (kvptsto_agree with "Hptsto Hown").
Qed.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_GetRPC (s args_ptr reply_ptr:loc) args γ Q :
  is_KVShardServer s γ -∗
  {{{
       own_GetRequest args_ptr args ∗
       (∃ dummy_rep, own_GetReply reply_ptr dummy_rep) ∗
       (PreShardGet γ.(kv_gn) args.(GR_Key) Q)
  }}}
    KVShardServer__GetRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_GetReply reply_ptr rep ∗
       (PostShardGet γ.(kv_gn) args.(GR_Key) Q) rep
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

  iDestruct (own_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
  set (sid:=shardOfC args.(GR_Key)) in *.

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
    iDestruct (slice.own_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
    iDestruct (big_sepS_elem_of_acc _ _ sid with "HownShards") as "[HownShard HownShards]".
    { set_solver. }
    iDestruct "HownShard" as "[%Hbad|HownShard]".
    { exfalso. done. }
    iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & %Hkvs_dom & HkvsMap & HvalSlices)".
    wp_apply (slice.wp_SliceGet _ _ _ _ _ _ _ (#kvs_ptr) with "[Hkvss_sl]").
    {
      iFrame "Hkvss_sl".
      iPureIntro.
      rewrite list_lookup_fmap.
      rewrite Hkvs_lookup.
      done.
    }
    iIntros "[Hkvss_sl %Hkvs_ty]".

    wp_apply (map.wp_MapGet with "[$HkvsMap]").
    iIntros (value okValue) "[%HlookupVal HkvsMap]".
    wp_pures.
    assert (value = default (slice_val Slice.nil) (mv !! args.(GR_Key))) as Hvalue.
    { naive_solver. }
    rewrite Hvalue.
    (*
      wp_apply (typed_slice.wp_NewSlice (V:=u8)).
      iIntros (val_sl') "Hval_sl".
      rewrite Hvalue.
     *)

    iDestruct (big_sepS_elem_of_acc _ _ args.(GR_Key) with "HvalSlices") as "[Hsrv_val_sl HvalSlices]".
    { set_solver. }
    iDestruct "Hsrv_val_sl" as "[%Hbad|Hsrv_val_sl]".
    { exfalso. naive_solver. }

    iDestruct "Hsrv_val_sl" as (?) "[%HvalSliceRe Hsrv_val_sl]".
    rewrite HvalSliceRe.
    (*
      iDestruct (typed_slice.own_slice_small_acc with "Hsrv_val_sl") as "[Hsrv_val_sl_small Hsrv_val_sl]".
     *)

    (*
      wp_apply (typed_slice.wp_SliceAppendSlice (V:=u8) with "[$Hval_sl $Hsrv_val_sl_small]").

      rewrite app_nil_l.
      iIntros (val_sl'') "[Hval_sl Hsrv_val_sl_small]".

      iSpecialize ("Hsrv_val_sl" with "Hsrv_val_sl_small").
     *)

    (* fill in reply struct *)
    wp_storeField.
    wp_pures.
    wp_storeField.

    wp_pures.
    (* commit *)
    unfold PreShardGet.
    iApply ncfupd_wp.
    iMod (ncfupd_mask_subseteq _) as "Hclose"; last iMod "Hpre".
    { done. }
    iDestruct "Hpre" as (v0) "(Hkvptsto & HfupdQ)".
    iDestruct (own_shard_agree with "HshardGhost Hkvptsto") as %Hmatch.
    { done. }
    (* match up with HshardGhost *)
    rewrite -Hmatch.
    iMod ("HfupdQ" with "Hkvptsto") as "Q".
    iMod "Hclose" as "_".

    iMod (own_slice_small_persist with "Hsrv_val_sl") as "#Hsrv_val_sl".

    iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
    iModIntro.
    wp_loadField.
    iApply wp_ncfupd.
    wp_apply (release_spec with "[-HΦ Q HErr HValue]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      iSplitL ""; first done.
      iSplitL ""; first done.
      iApply "HownShards".
      iRight.
      iExists _, _, _.
      iFrame.
      iSpecialize ("HvalSlices" with "[]").
      {
        iRight. iExists _; iFrame "#". done.
      }
      iFrame "HvalSlices".
      done.
    }
    wp_pures. iApply "HΦ".
    instantiate (1:= mkGetReplyC _ _).
    iSplitL "HErr HValue".
    {
      iExists _; iFrame "∗#". done.
    }
    iRight.
    iSimpl.
    by iFrame.
  }
  { (* don't have shard *)
    wp_storeField.

    wp_loadField.
    iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
    iApply wp_ncfupd.
    wp_apply (release_spec with "[> -HΦ Hpre HValue HErr]").
    {
      iFrame "HmuInv Hlocked".
      iModIntro. iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      done.
    }
    wp_pures. iModIntro. iApply "HΦ".
    iSplitL "HErr HValue".
    {
      iExists _.
      instantiate (1:=mkGetReplyC _ _).
      by iFrame.
    }
    iLeft.
    iSimpl.
    by iFrame.
  }
Qed. (* FIXME Qed takes forever, why that? *)

End memkv_shard_proof.

Ltac Zify.zify_post_hook ::= idtac.
