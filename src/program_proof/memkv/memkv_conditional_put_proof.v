From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

Section memkv_conditional_put_proof.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, HREG: rpcregG Σ, kvMapG Σ}.

Local Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.

Lemma wp_ConditionalPutRPC (s args_ptr reply_ptr:loc) expv_sl newv_sl args γ γreq Q :
  is_MemKVShardServer s γ -∗
  {{{
       own_ConditionalPutRequest args_ptr expv_sl newv_sl args ∗
       (∃ dummy_rep, own_ConditionalPutReply reply_ptr dummy_rep) ∗
       is_RPCRequest γ.(rpc_gn) γreq (PreShardConditionalPut γ.(kv_gn) args.(CPR_Key) Q args.(CPR_ExpValue) args.(CPR_NewValue))
                                (PostShardConditionalPut γ.(kv_gn) args.(CPR_Key) Q args.(CPR_ExpValue) args.(CPR_NewValue))
                                {| Req_CID:=args.(CPR_CID); Req_Seq:=args.(CPR_Seq) |}
  }}}
    MemKVShardServer__ConditionalPutRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_ConditionalPutReply reply_ptr rep ∗
       (RPCRequestStale γ.(rpc_gn) {| Req_CID:=args.(CPR_CID); Req_Seq:=args.(CPR_Seq) |} ∨
        ∃ dummy_val, RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=args.(CPR_CID); Req_Seq:=args.(CPR_Seq) |} (mkShardReplyC rep.(CPR_Err) dummy_val rep.(CPR_Succ)))
  }}}.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & Hrep & #HreqInv)".
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

  wp_loadField. wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (seqno ok) "[%HseqGet HlastSeqMap]".
  wp_pures.

  wp_loadField.
  wp_pures.

  wp_apply (wp_and ok (int.Z args.(CPR_Seq) ≤ int.Z seqno)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }

  wp_if_destruct.
  { (* reply table *)
    wp_loadField.
    wp_loadField.
    wp_apply (map.wp_MapGet with "HlastReplyMap").
    iIntros (reply replyOk) "[%HlookupReply HlastReplyMap]".
    wp_pures.
    Transparent struct.store.
    unfold struct.store.
    Opaque struct.store.
    Opaque struct.t.
    wp_pures.

    destruct ok; last first.
    { exfalso. naive_solver. }
    apply map_get_true in HseqGet.
    destruct Heqb as [_ HseqLe].

    (* get a copy of the is_slice for the slice we're giving in reply *)
    assert (is_Some (lastReplyMV !! args.(CPR_CID))) as [? HlastReplyMVlookup].
    {
      assert (args.(CPR_CID) ∈ dom (gset u64) lastSeqM).
      { by eapply elem_of_dom_2. }
      assert (args.(CPR_CID) ∈ dom (gset u64) lastReplyMV).
      { rewrite -HlastReplyMVdom in H1. done. }
      apply elem_of_dom.
      done.
    }

    iDestruct (big_sepM2_lookup_iff with "HlastReply_structs") as %Hdom.
    assert (is_Some (lastReplyM !! args.(CPR_CID))) as [? HlastReplyMlookup].
    { apply Hdom. naive_solver. }

    iDestruct (big_sepM2_lookup_acc _ _ _ args.(CPR_CID) with "HlastReply_structs") as "[HlastReply_struct HlastReply_structs]".
    {
      done.
    }
    {
      done.
    }

    iDestruct "HlastReply_struct" as (srv_val_sl ?) "[%Hx Hsrv_val_sl]".
    assert (x = reply) as ->.
    {
      unfold map.map_get in HlookupReply.
      rewrite HlastReplyMVlookup in HlookupReply.
      naive_solver.
    }

    rewrite Hx.
    Opaque typed_slice.is_slice_small. (* to split fraction *)
    iDestruct "Hsrv_val_sl" as "[Hsrv_val_sl Hrep_val_sl]".
    Transparent typed_slice.is_slice_small.
    iSpecialize ("HlastReply_structs" with "[Hsrv_val_sl]").
    {
      iExists _, _.
      iFrame.
      done.
    }
    wp_storeField.
    wp_storeField.

    (* now split into stale/nonstale cases *)
    destruct (Z.lt_ge_cases (int.Z args.(CPR_Seq)) (int.Z seqno)) as [Hcase|Hcase].
    { (* Stale *)
      iMod (smaller_seqno_stale_fact _ {| Req_CID:=_; Req_Seq:=_ |} seqno with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { done. }
      iDestruct "HH" as "[Hrpc #Hstale]".
      wp_loadField.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HExpValue_sl HNewValue_sl HErr HSucc Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        done.
      }
      iApply "HΦ".

      iSplitL "HErr HSucc".
      {
        instantiate (1:={| CPR_Err := _ |}).
        iFrame.
      }
      iLeft.
      iFrame "#".
    }
    { (* Not stale *)
      assert (seqno = args.(CPR_Seq)) by word.
      rewrite H1 in HseqGet.
      iMod (server_replies_to_request _ {| Req_CID:=_; Req_Seq:=_ |} with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { eexists (mkShardReplyC 0 [] false). naive_solver. }

      iDestruct "HH" as "[#Hreceipt Hrpc]".

      (* prove that args.(GR_CID) is in lastReplyMV (probably just add [∗ map] _ ↦ _;_ ∈ lastReplyMV ; lastSeq, True) *)
      wp_loadField.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HExpValue_sl HNewValue_sl HErr HSucc Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        done.
      }
      iApply "HΦ".
      iSplitL "HErr HSucc".
      {
        instantiate (1:={| CPR_Err := _ |}).
        by iFrame.
      }
      iRight.
      rewrite HlastReplyMlookup.
      simpl.
      destruct x0.
      iExists _.
      iFrame "#".
    }
  }
  {
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert with "HlastSeqMap").
    { done. }
    iIntros "HlastSeqMap".

    wp_pures.
    wp_loadField.
    wp_apply (wp_shardOf).
    wp_pures.
    wp_loadField.

    iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
    set (sid:=shardOfC args.(CPR_Key)) in *.

    assert (∃ b, shardMapping !! int.nat sid = Some b) as [? ?].
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

    assert (int.Z seqno < int.Z args.(CPR_Seq))%Z as HseqFresh.
    {
      simpl.
      destruct ok.
      {
        intuition.
        destruct (Z.le_gt_cases (int.Z args.(CPR_Seq)) (int.Z seqno)) as [Hineq|Hineq].
        { naive_solver. }
        { naive_solver. }
      }
      {
        apply map_get_false in HseqGet as [_ ->].
        simpl.
        word.
      }
    }

    (* get resources out of escrow before splitting into cases *)
    iMod (server_takes_request with "HreqInv Hrpc") as "HH".
    { done. }
    {
      rewrite HseqGet.
      done.
    }
    iDestruct "HH" as "(Hγpre & Hpre & Hproc)".

    wp_if_destruct.
    { (* have the shard *)
      wp_loadField.
      iDestruct (is_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
      iDestruct (big_sepS_elem_of_acc _ _ sid with "HownShards") as "[HownShard HownShards]".
      { set_solver. }
      iDestruct "HownShard" as "[%Hbad|HownShard]".
      { exfalso. done. }
      iDestruct "HownShard" as (kvs_ptr m mv) "(HshardGhost & %Hkvs_lookup & HkvsMap & HvalSlices)".
      wp_apply (wp_SliceGet _ _ _ _ _ _ _ (#kvs_ptr) with "[Hkvss_sl]").
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
      iDestruct "Hsrv_val_sl" as (q curv_sl) "[%HvalSliceRe Hsrv_val_sl]".
      rewrite HvalSliceRe.

      wp_loadField.
      iMod (readonly_load with "HExpValue_sl") as (?) "HExpValue_sl'".
      (*
      iDestruct (is_slice_small_acc with "Hsrv_val_sl") as "[Hsrv_val_sl Hsrv_val_close]".
       *)
      wp_apply (wp_BytesEqual with "[$HExpValue_sl' $Hsrv_val_sl]").
      iIntros "[_ Hsrv_val_sl]".

      (* Avoid duplicating the proof of the merged control flow after this if *)
      wp_apply (wp_If_join_evar with "[HkvsMap HKey HNewValue]").
      { iIntros (succ Hsucc).
        case_bool_decide as Heq; wp_pures.
        - wp_loadField.
          wp_loadField.
          set (old_map := (mv, _)).
          wp_apply (map.wp_MapInsert with "[$HkvsMap]").
          iIntros "HkvsMap".
          wp_pures. iModIntro.
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
      rewrite global_groveG_inv_conv'.
      iApply ncfupd_wp.
      iMod (ncfupd_mask_subseteq _) as "Hclose"; last iMod "Hpre".
      { done. }
      iDestruct "Hpre" as (v0) "(Hkvptsto2 & HfupdQ)".
      iDestruct (kvptsto_agree with "Hkvptsto Hkvptsto2") as %<-.
      set (newv := if succ then args.(CPR_NewValue) else (default [] (m !! args.(CPR_Key)))).
      iMod (kvptsto_update newv with "Hkvptsto Hkvptsto2") as "[Hkvptsto Hkvptsto2]".
      iMod ("HfupdQ" with "Hkvptsto") as "Q".
      iMod "Hclose" as "_".

      (* fill in reply struct *)
      iModIntro.
      wp_loadField.
      wp_loadField.
      wp_loadField.
      wp_loadField.

      (* save reply in reply table *)
      Transparent struct.load.
      unfold struct.load.

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".

      wp_pures.

      iMod (server_completes_request with "His_srv HreqInv Hγpre [Q] Hproc") as "HH".
      { done. }
      { done. }
      { rewrite HseqGet. simpl. done. }
      {
        iNext.
        iRight.
        iFrame.
        instantiate (1:=mkShardReplyC _ [] succ).
        simpl.
        eauto.
      }
      iDestruct "HH" as "(#Hreceipt & Hrpc)".

      iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
      wp_loadField.
      iMod (readonly_load with "HNewValue_sl") as (?) "HNewValue_sl'".
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HErr HSucc]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        iSplitL "".
        {
          iPureIntro.
          simpl.
          rewrite !dom_insert_L.
          congruence.
        }
        iSplitL "HlastReply_structs".
        {
          iApply (big_sepM2_insert_2 with "[] HlastReply_structs").
          { simpl.
            iExists _, 1%Qp.
            rewrite zero_slice_val.
            iSplitL ""; first done.
            iApply (typed_slice.is_slice_small_nil).
            done.
          }
        }
        iSplitL ""; first done.
        iSplitL ""; first done.
        iApply "HownShards".
        iRight.
        iExists _, _, _.
        iFrame.
        instantiate (1:=(<[args.(CPR_Key):=newv]> m)).
        iSplitL "HshardGhost Hkvptsto2".
        {
          iApply (big_sepS_delete _ _ args.(CPR_Key) with "[-]").
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
        iSplitL "HkvsMap".
        { instantiate (1:=if succ then _ else _).
          destruct succ; done. }
        iApply (big_sepS_delete _ _ args.(CPR_Key) with "[-]").
        { set_solver. }
        simpl. iSplitL "HNewValue_sl' Hsrv_val_sl".
        {
          simpl. iRight. destruct succ.
          - iExists _, newv_sl.
            rewrite lookup_insert.
            rewrite lookup_insert.
            eauto with iFrame.
          - iExists _, curv_sl.
            rewrite lookup_insert.
            eauto with iFrame.
        }
        iApply (big_sepS_impl with "HvalSlices").
        iModIntro.
        iIntros.
        rewrite lookup_insert_ne; last first.
        { set_solver. }
        destruct succ.
        - rewrite lookup_insert_ne; last first.
          { set_solver. }
          iFrame.
        - iFrame.
      }
      iApply "HΦ".
      iSplitL "HErr HSucc".
      {
        instantiate (1:=mkConditionalPutReplyC _ _).
        iFrame.
      }
      iSimpl.
      iRight.
      iExists [].
      iFrame "#".
    }
    { (* don't have shard *)
      wp_storeField.

      iMod (server_completes_request with "His_srv HreqInv Hγpre [Hpre] Hproc") as "HH".
      { done. }
      { done. }
      { rewrite HseqGet. simpl. done. }
      {
        iNext.
        iLeft.
        iFrame "Hpre".
        instantiate (1:=mkShardReplyC 1 [] _).
        simpl.
        done.
      }
      iDestruct "HH" as "(#Hreceipt & Hrpc)".

      Transparent struct.load.
      unfold struct.load.
      wp_loadField.
      wp_loadField.
      wp_loadField.
      wp_loadField.
      rewrite zero_slice_val.

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".
      wp_pures.

      wp_loadField.
      iSpecialize ("HshardMap_sl_close" with "HshardMap_sl").
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HErr HSucc]").
      {
        iFrame "HmuInv Hlocked".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        iSplitL "".
        { iPureIntro.
          rewrite !dom_insert_L /=.
          congruence. }
        iSplitL "HlastReply_structs".
        {
          iApply (big_sepM2_insert_2 with "[] HlastReply_structs").
          simpl.
          iExists Slice.nil, 1%Qp; iFrame.
          iSplitL ""; first done.
          iApply (typed_slice.is_slice_small_nil).
          done.
        }
        done.
      }
      iApply "HΦ".
      iSplitL "HErr HSucc".
      {
        instantiate (1:=mkConditionalPutReplyC _ _).
        iFrame.
      }
      iSimpl.
      iRight.
      iExists []; iFrame "Hreceipt".
    }
  }
Qed.

End memkv_conditional_put_proof.

Ltac Zify.zify_post_hook ::= idtac.
