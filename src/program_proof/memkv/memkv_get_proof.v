From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

Section memkv_shard_proof.

Context `{!heapGS Σ, rpcG Σ ShardReplyC, HREG: rpcregG Σ, kvMapG Σ}.

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

Lemma wp_GetRPC (s args_ptr reply_ptr:loc) args γ γreq Q :
  is_KVShardServer s γ -∗
  {{{
       own_GetRequest args_ptr args ∗
       (∃ dummy_rep, own_GetReply reply_ptr dummy_rep) ∗
       is_RPCRequest γ.(rpc_gn) γreq (PreShardGet γ.(kv_gn) args.(GR_Key) Q)
                                (PostShardGet γ.(kv_gn) args.(GR_Key) Q)
                                {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |}
  }}}
    KVShardServer__GetRPC #s #args_ptr #reply_ptr
  {{{
       rep, RET #();
       own_GetReply reply_ptr rep ∗
       (RPCRequestStale γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} ∨
        ∃ dummy_succ, RPCReplyReceipt γ.(rpc_gn) {| Req_CID:=args.(GR_CID); Req_Seq:=args.(GR_Seq) |} (mkShardReplyC rep.(GR_Err) rep.(GR_Value) dummy_succ))
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
  iIntros (v ok) "[%HseqGet HlastSeqMap]".
  wp_pures.

  wp_loadField.
  wp_pures.

  wp_apply (wp_and_pure ok (int.Z args.(GR_Seq) ≤ int.Z v)%Z).
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
(*
    iAssert (reply_ptr ↦[struct.t GetReply] (#_, (slice_val val_sl, #())) )%I with "[HValue HErr]" as "Hrep".
    {
      iApply struct_fields_split.
      iFrame.
      done.
    }
*)
    destruct ok; last first.
    { exfalso. naive_solver. }
    apply map_get_true in HseqGet.
    destruct Heqb as [_ HseqLe].

    (* get a copy of the is_slice for the slice we're giving in reply *)
    assert (is_Some (lastReplyMV !! args.(GR_CID))) as [? HlastReplyMVlookup].
    {
      assert (args.(GR_CID) ∈ dom (gset u64) lastSeqM).
      { by eapply elem_of_dom_2. }
      assert (args.(GR_CID) ∈ dom (gset u64) lastReplyMV).
      { rewrite -HlastReplyMVdom in H1. done. }
      apply elem_of_dom.
      done.
    }

    iDestruct (big_sepM2_lookup_iff with "HlastReply_structs") as %Hdom.
    assert (is_Some (lastReplyM !! args.(GR_CID))) as [? HlastReplyMlookup].
    { apply Hdom. naive_solver. }

    iDestruct (big_sepM2_lookup_acc _ _ _ args.(GR_CID) with "HlastReply_structs") as "[HlastReply_struct HlastReply_structs]".
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
    iDestruct "Hsrv_val_sl" as "[Hsrv_val_sl Hrep_val_sl]".
    iSpecialize ("HlastReply_structs" with "[Hsrv_val_sl]").
    {
      iExists _, _.
      iFrame.
      done.
    }
    (* Now we have a fraction of the slice we were looking for *)
    wp_storeField.
    wp_pures.
    Transparent slice.T.
    wp_storeField.
    Opaque slice.T.
    wp_pures.

    (* now split into stale/nonstale cases. FIXME: there is still a bunch of duplication here, use lemma for if-with-merging-control-flow? *)
    destruct (Z.lt_ge_cases (int.Z args.(GR_Seq)) (int.Z v)) as [Hcase|Hcase].
    { (* Stale *)
      iMod (smaller_seqno_stale_fact _ {| Req_CID:=_; Req_Seq:=_ |} v with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { done. }
      iDestruct "HH" as "[Hrpc #Hstale]".
      wp_loadField.
      iApply wp_ncfupd.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HValue_sl HValue HErr Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iApply "HΦ".

      iSplitL "HErr HValue Hrep_val_sl".
      {
        instantiate (1:={| GR_Err := _ |}).
        iExists _; iFrame.
        (* FIXME: we are readonly_alloc'ing several times here; we should probably push
           this up to wherever the is_slice_small is coming from. *)
        iMod (readonly_alloc with "[Hrep_val_sl]") as "$"; by iFrame.
      }
      iLeft.
      by iFrame "#".
    }
    { (* Not stale *)
      assert (v = args.(GR_Seq)) by word.
      rewrite H1 in HseqGet.
      iMod (server_replies_to_request _ {| Req_CID:=_; Req_Seq:=_ |} with "His_srv Hrpc") as "HH".
      { done. }
      { done. }
      { eexists (mkShardReplyC 0 [] false). naive_solver. }

      iDestruct "HH" as "[#Hreceipt Hrpc]".

      (* prove that args.(GR_CID) is in lastReplyMV (probably just add [∗ map] _ ↦ _;_ ∈ lastReplyMV ; lastSeq, True) *)
      wp_loadField.
      iApply wp_ncfupd.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey HValue_sl HValue HErr Hrep_val_sl]").
      {
        iFrame "#∗".
        iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        done.
      }
      wp_pures. iApply "HΦ".
      iSplitL "HErr HValue Hrep_val_sl".
      {
        instantiate (1:={| GR_Err := _ |}).
        iExists _; iFrame.
        iMod (readonly_alloc with "[Hrep_val_sl]") as "$"; by iFrame.
      }
      iRight.
      rewrite HlastReplyMlookup.
      simpl.
      destruct x0.
      iExists _.
      by iFrame "#".
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

    iDestruct (is_slice_small_acc with "HshardMap_sl") as "[HshardMap_sl HshardMap_sl_close]".
    set (sid:=shardOfC args.(GR_Key)) in *.

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

    (* get resources out of escrow before splitting into cases *)
    iMod (server_takes_request with "HreqInv Hrpc") as "HH".
    { done. }
    {
      rewrite HseqGet.
      simpl.
      destruct ok.
      {
        apply map_get_true in HseqGet.
        edestruct (Z.le_gt_cases (int.Z args.(GR_Seq)) (int.Z v)) as [Hineq|Hineq].
        { exfalso. naive_solver. }
        { done. }
      }
      {
        apply map_get_false in HseqGet as [_ HseqGet].
        rewrite HseqGet.
        simpl.
        word.
      }
    }
    iDestruct "HH" as "(Hγpre & Hpre & Hproc)".

    assert (int.Z v < int.Z args.(GR_Seq))%Z as HseqFresh.
    {
      simpl.
      destruct ok.
      {
        intuition.
        destruct (Z.le_gt_cases (int.Z args.(GR_Seq)) (int.Z v)) as [Hineq|Hineq].
        { naive_solver. }
        { naive_solver. }
      }
      {
        apply map_get_false in HseqGet as [_ ->].
        simpl.
        word.
      }
    }

    wp_if_destruct.
    { (* have the shard *)
      wp_loadField.
      wp_loadField.
      iDestruct (is_slice_split with "Hkvss_sl") as "[Hkvss_sl Hkvss_sl_close]".
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

      iDestruct "Hsrv_val_sl" as (q ?) "[%HvalSliceRe Hsrv_val_sl]".
      rewrite HvalSliceRe.
      (*
      iDestruct (typed_slice.is_slice_small_acc with "Hsrv_val_sl") as "[Hsrv_val_sl_small Hsrv_val_sl]".
       *)

      (*
      wp_apply (typed_slice.wp_SliceAppendSlice (V:=u8) with "[$Hval_sl $Hsrv_val_sl_small]").

      rewrite app_nil_l.
      iIntros (val_sl'') "[Hval_sl Hsrv_val_sl_small]".

      iSpecialize ("Hsrv_val_sl" with "Hsrv_val_sl_small").
       *)

      (* fill in reply struct *)
      wp_apply (wp_storeField with "HValue").
      { apply slice_val_ty. }
      iIntros "HValue".
      wp_pures.
      wp_storeField.

      (* save reply in reply table *)
      Transparent struct.load.
      unfold struct.load.

      wp_loadField.
      wp_loadField.
      wp_loadField.
      wp_loadField.

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".

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


      iMod (server_completes_request with "His_srv HreqInv Hγpre [Q] Hproc") as "HH".
      { done. }
      { done. }
      { rewrite HseqGet. simpl. done. }
      {
        iNext.
        iRight.
        instantiate (1:=mkShardReplyC _ _ _).
        iFrame "Q".
        simpl.
        done.
      }
      iDestruct "HH" as "(#Hreceipt & Hrpc)".
      iModIntro.

      iDestruct "Hsrv_val_sl" as "[Hsrv_val_sl Hval_sl]".

      iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
      wp_loadField.
      iDestruct "Hval_sl" as "[Hrep_val_sl Hsrv_rep_val_sl]".
      iApply wp_ncfupd.
      wp_apply (release_spec with "[-HΦ HCID HSeq HKey Hrep_val_sl HErr HValue]").
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
        iSplitL "HlastReply_structs Hsrv_rep_val_sl".
        {
          iApply (big_sepM2_insert_2 with "[Hsrv_rep_val_sl] HlastReply_structs").
          { simpl.
            iExists _, _.
            iFrame.
            done.
          }
        }
        iSplitL ""; first done.
        iSplitL ""; first done.
        iApply "HownShards".
        iRight.
        iExists _, _, _.
        iFrame.
        iSpecialize ("HvalSlices" with "[Hsrv_val_sl]").
        {
          iRight. iExists _, _; iFrame. done.
        }
        iFrame "HvalSlices".
        done.
      }
      wp_pures. iApply "HΦ".
      instantiate (1:= mkGetReplyC _ _).
      iSplitL "HErr HValue Hrep_val_sl".
      {
        iExists _; iFrame.
        iMod (readonly_alloc with "[Hrep_val_sl]") as "$"; by iFrame.
      }
      iSimpl.
      iRight. iExists _.
      by iFrame "#".
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
        instantiate (1:=mkShardReplyC 1 dummy_rep.(GR_Value) false).
        iFrame "Hpre".
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

      wp_apply (map.wp_MapInsert with "HlastReplyMap").
      iIntros "HlastReplyMap".
      wp_pures.

      wp_loadField.
      iDestruct ("HshardMap_sl_close" with "HshardMap_sl") as "HshardMap_sl".
      iApply wp_ncfupd.
      wp_apply (release_spec with "[> -HΦ HCID HSeq HKey HValue HErr]").
      {
        iFrame "HmuInv Hlocked".
        iMod (readonly_load with "HValue_sl") as (?) "HValue_sl'".
        iModIntro. iNext.
        iExists _,_,_, _, _, _, _, _.
        iExists _, _, _, _.
        iFrame.
        iSplitL "".
        { iPureIntro.
          rewrite !dom_insert_L /=.
          congruence. }
        iSplitL "HlastReply_structs HValue_sl'".
        {
          iApply (big_sepM2_insert_2 with "[HValue_sl'] HlastReply_structs").
          simpl.
          iExists _, _; iFrame.
          done.
        }
        done.
      }
      wp_pures. iModIntro. iApply "HΦ".
      iSplitL "HErr HValue".
      {
        iExists _.
        instantiate (1:=mkGetReplyC _ _).
        by iFrame.
      }
      iSimpl.
      iRight. iExists _.
      by iFrame "#".
    }
  }
Qed. (* FIXME Qed takes forever, why that? *)

End memkv_shard_proof.

Ltac Zify.zify_post_hook ::= idtac.
