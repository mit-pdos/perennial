From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

#[local] Set Universe Polymorphism.

Section memkv_conditional_put_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_ConditionalPutRPC (s args_ptr reply_ptr:loc) expv_sl newv_sl args Q γ :
  is_KVShardServer s γ -∗
  {{{
       own_ConditionalPutRequest args_ptr expv_sl newv_sl args ∗
       (∃ dummy_rep, own_ConditionalPutReply reply_ptr dummy_rep) ∗
       PreShardConditionalPut γ.(kv_gn) args.(CPR_Key) Q args.(CPR_ExpValue) args.(CPR_NewValue)
  }}}
    KVShardServer__ConditionalPutRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_ConditionalPutReply reply_ptr rep ∗
       PostShardConditionalPut γ.(kv_gn) args.(CPR_Key) Q args.(CPR_ExpValue) args.(CPR_NewValue) rep
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
  set (sid:=shardOfC args.(CPR_Key)) in *.

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
    iDestruct (slice.own_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
    iDestruct (big_sepS_elem_of_acc _ _ sid with "HownShards") as "[HownShard HownShards]".
    { set_solver. }
    iDestruct "HownShard" as "[%Hbad|HownShard]".
    { exfalso. done. }
    iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & %Hdom_kvs& HkvsMap & HvalSlices)".
    wp_apply (slice.wp_SliceGet _ _ _ _ _ _ _ (#kvs_ptr) with "[Hkvss_sl]").
    {
      iFrame "Hkvss_sl".
      iPureIntro.
      rewrite list_lookup_fmap.
      rewrite Hkvs_lookup.
      done.
    }
    iIntros "[Hkvss_sl %Hkvs_ty]".

    wp_loadField.
    wp_apply (map.wp_MapGet with "[$HkvsMap]").
    iIntros (value okValue) "[%HlookupVal HkvsMap]".
    assert (value = default (slice_val Slice.nil) (mv !! args.(CPR_Key))) as ->.
    { naive_solver. }
    iDestruct (big_sepS_delete _ _ args.(CPR_Key) with "HvalSlices") as "[Hsrv_val_sl HvalSlices]".
    { set_solver. }
    iDestruct "Hsrv_val_sl" as "[%Hbad|Hsrv_val_sl]".
    { exfalso. naive_solver. }
    iDestruct "Hsrv_val_sl" as (curv_sl) "[%HvalSliceRe #Hsrv_val_sl]".
    rewrite HvalSliceRe.

    wp_loadField.
    wp_apply (wp_BytesEqual with "[HExpValue_sl Hsrv_val_sl]").
    { iFrame "∗#". }
    iIntros "[_ Hsrv_val_sl']".

    (* Avoid duplicating the proof of the merged control flow after this if *)
    wp_apply (wp_If_join_evar with "[HkvsMap HKey HNewValue]").
    { iIntros (succ Hsucc).
      case_bool_decide as Heq; wp_pures.
      - wp_loadField.
        wp_loadField.
        set (old_map := (mv, _)).
        wp_apply (map.wp_MapInsert with "[$HkvsMap]").
        iIntros "HkvsMap".
        wp_pures.
        iSplit; first done.
        set (new_map := map.map_insert _ args.(CPR_Key) _).
        replace (new_map) with (if succ then new_map else old_map); last by rewrite Hsucc.
        iNamedAccu.
      - iModIntro. iSplit; first done.
        rewrite Hsucc.
        iFrame. }
    iIntros "Hjoined". iNamed "Hjoined".
    set (succ := bool_decide (_ = _)).

    wp_storeField.
    wp_storeField.
    iDestruct (big_sepS_delete _ _ args.(CPR_Key) with "HshardGhost") as "[Hghost HshardGhost]".
    { set_solver. }
    iDestruct "Hghost" as "[%Hbad|Hkvptsto]".
    { exfalso; done. }

    (* Get Q by using fupd *)
    unfold PreShardConditionalPut.
    iApply ncfupd_wp.
    iMod (ncfupd_mask_subseteq _) as "Hclose"; last iMod "Hpre".
    { done. }
    iDestruct "Hpre" as (v0) "(Hkvptsto2 & HfupdQ)".
    iDestruct (kvptsto_agree with "Hkvptsto Hkvptsto2") as %<-.
    set (newv := if succ then args.(CPR_NewValue) else (default [] (m !! args.(CPR_Key)))).
    iMod (kvptsto_update newv with "Hkvptsto Hkvptsto2") as "[Hkvptsto Hkvptsto2]".
    iMod ("HfupdQ" with "Hkvptsto") as "Q".
    iMod "Hclose" as "_".

    iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
    iModIntro.
    wp_loadField.
    wp_apply (release_spec with "[-HΦ HKey HErr HSucc Q]").
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
      instantiate (1:=(if succ then <[args.(CPR_Key):=args.(CPR_NewValue)]> m else m)).
      iSplitL "HshardGhost Hkvptsto2".
      {
        iApply (big_sepS_delete _ _ args.(CPR_Key) with "[-]").
        { set_solver. }
        iSplitL "Hkvptsto2".
        {
          iRight.
          destruct succ.
          * rewrite lookup_insert. iFrame.
          * iFrame.
        }
        iApply (big_sepS_impl with "HshardGhost").
        iModIntro; iIntros.
        destruct succ.
        * rewrite lookup_insert_ne; last first.
          { set_solver. }
          iFrame.
        * iFrame.
      }
      iSplitL ""; first done.
      iSplitL ""; last first.
      { iSplitL "HkvsMap".
        { instantiate (1:=if succ then _ else _).
          destruct succ; done. }
        iApply (big_sepS_delete _ _ args.(CPR_Key) with "[-]").
        { set_solver. }
        simpl. iSplitL "HNewValue_sl Hsrv_val_sl".
        {
          simpl. iRight. destruct succ.
          - iExists newv_sl.
            rewrite lookup_insert.
            rewrite lookup_insert.
            eauto with iFrame.
          - iExists curv_sl.
            eauto with iFrame.
        }
        iApply (big_sepS_impl with "HvalSlices").
        iModIntro.
        iIntros.
        destruct succ.
        * rewrite ?lookup_insert_ne; last first.
          { set_solver. }
          { set_solver. }
          iFrame "∗#".
        * iFrame "∗#".
      }
      destruct succ; rewrite ?dom_insert_L; iPureIntro; congruence.
    }
    wp_pures. iApply "HΦ". iModIntro.
    iSplitL "HErr HSucc".
    {
      instantiate (1:=mkConditionalPutReplyC _ _).
      iFrame.
    }
    iRight.
    iSimpl.
    iFrame "Q".
    done.
  }
  { (* don't have shard *)
    wp_storeField.

    wp_loadField.
    iSpecialize ("HshardMap_sl_close" with "HshardMap_sl").
    wp_apply (release_spec with "[-HΦ HKey HErr HSucc Hpre]").
    {
      iFrame "HmuInv Hlocked".
      iNext.
      iExists _,_,_, _, _, _.
      iFrame.
      done.
    }
    wp_pures. iApply "HΦ". iModIntro.
    iSplitL "HErr HSucc".
    {
      instantiate (1:=mkConditionalPutReplyC _ _).
      iFrame.
    }
    iLeft.
    iSimpl.
    iFrame.
    done.
  }
Qed.

End memkv_conditional_put_proof.

Ltac Zify.zify_post_hook ::= idtac.
