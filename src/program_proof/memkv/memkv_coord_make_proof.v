From Perennial.Helpers Require Import range_set.
From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

Section memkv_coord_make_proof.

Context `{!heapG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Record memkv_coord_names := {
 coord_rpc_gn : rpc_names ;
 coord_urpc_gn : server_chan_gnames ;
 coord_kv_gn : gname
}
.

Lemma wp_MakeMemKVCoordServer (initserver : u64) (γ : memkv_coord_names) γinit :
  {{{
       "%Hinitserver_gnames" ∷ ⌜γinit.(kv_gn) = γ.(coord_kv_gn)⌝ ∗
       "#Hinit_is_shard_server" ∷ is_shard_server initserver γinit ∗
       "#His_srv" ∷ is_RPCServer γ.(coord_rpc_gn) ∗
       "HRPCserver_own" ∷ RPCServer_own_ghost γ.(coord_rpc_gn) ∅ ∅ ∗
       "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), RPCClient_own_ghost γ.(coord_rpc_gn) cid 1
  }}}
    MakeMemKVCoordServer #initserver
  {{{
       s, RET #s; True%I
       (* TODO: this is obviously not the correct postcondition *)
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.  Opaque slice.T. }
  iIntros (s) "srv".
  wp_pures.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  iDestruct (struct_fields_split with "srv") as "srv". iNamed "srv".
  wp_storeField.
  wp_apply (typed_slice.wp_NewSlice (V:=u64)).
  iIntros (shardMap_sl) "HshardMap_sl".
  Transparent slice.T. wp_storeField. Opaque slice.T.
  remember (replicate (int.nat 65536) IntoVal_def) as initShardMapping eqn:Heq_initShardMapping.
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (iptr) "Hi".
  wp_pures.
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ shardMapping,
  "%Hlen_shardMapping" ∷ ⌜ Z.of_nat (length shardMapping) = uNSHARD ⌝ ∗
  "%HshardMapping_dom" ∷ ⌜ (∀ i : u64, int.Z i < int.Z uNSHARD → is_Some (shardMapping !! int.nat i)) ⌝ ∗
  "shardMap" ∷ s ↦[MemKVCoord :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ @typed_slice.is_slice grove_op grove_model grove_interp Σ heapG0 grove_ty u64
                     (@u64_IntoVal grove_op) shardMap_sl HostName 1 shardMapping ∗
  "HownShards" ∷ ([∗ set] sid ∈ rangeSet 0 uNSHARD, ∃ (hid : u64),
                  ⌜ shardMapping !! int.nat sid = Some hid ⌝ ∗
                  (⌜ hid = 0 ⌝ ∨ ∃ hγ, ⌜ hγ.(kv_gn) = γ.(coord_kv_gn) ⌝ ∗ is_shard_server hid hγ)
                  ))%I with "[] [$Hi HshardMap_sl shardMap]").
  { word. }
  { iIntros (i Φ') "!# H HΦ".
    iDestruct "H" as "(H1&H2)".
    iNamed "H1".
    iDestruct "H2" as "(Hi&%Hbound)".
    wp_pures.
    wp_apply (wp_LoadAt with "[$Hi]").
    iIntros "Hi".
    wp_loadField.
    iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "(HshardMap_sl&HshardMap_sl_close)".
    wp_apply (typed_slice.wp_SliceSet (V:=u64) with "[$HshardMap_sl]").
    { eauto. }
    iIntros "HshardMap_sl".
    iDestruct ("HshardMap_sl_close" with "[$HshardMap_sl]") as "HshardMap_sl".
    wp_pures. iModIntro. iApply "HΦ".
    remember uNSHARD as uNSHARD' eqn:Heq_uNSHARD.
    { iFrame. iExists _. iFrame.
      iSplit.
      { iPureIntro. rewrite insert_length //. }
      iSplit.
      { iPureIntro. intros.
        destruct (decide (int.nat i0 = int.nat i)) as [->|Hneq].
        { eexists. apply list_lookup_insert. eapply lookup_lt_is_Some_1; eauto.
          apply HshardMapping_dom. rewrite Heq_uNSHARD. eauto.
        }
        rewrite list_lookup_insert_ne; auto.
      }
      assert (i ∈ (rangeSet 0 uNSHARD')).
      {
        apply rangeSet_lookup; try word.
        - rewrite Heq_uNSHARD /uNSHARD. word.
        - rewrite Heq_uNSHARD /uNSHARD. word.
      }
      assert (rangeSet 0 uNSHARD' = {[i]} ∪ ((rangeSet 0 uNSHARD' : gset u64) ∖ {[i]})) as Heq_diff.
      { apply union_difference_singleton_L; eauto. }
      iEval (rewrite Heq_diff) in "HownShards".
      iEval (rewrite Heq_diff).
      iApply big_sepS_union.
      { set_solver+. }
      iDestruct (big_sepS_union with "HownShards") as "(Hi&HownShards)".
      { set_solver+. }
      iSplitL "Hi".
      { rewrite ?big_sepS_singleton.
        rewrite list_lookup_insert //; last first.
        { eapply lookup_lt_is_Some_1; eauto.
          apply HshardMapping_dom. rewrite Heq_uNSHARD. eauto.
        }
        iExists _. iFrame "#". eauto. }
      iApply (big_sepS_mono with "HownShards").
      { iIntros (? Hin) "H".
        assert (int.nat i ≠ int.nat x).
        { cut (i ≠ x).
          { intros. intros Heq. apply Z2Nat.inj in Heq; try word.
             apply int_Z_inj in Heq; eauto with *.
          }
          move:Hin. set_solver+. }
        rewrite ?list_lookup_insert_ne //.
      }
    }
  }
  {
    iExists _. iFrame.
    iSplit.
    { iPureIntro. rewrite Heq_initShardMapping replicate_length /uNSHARD. word. }
    iSplit.
    { iPureIntro. rewrite /uNSHARD. intros i Hlt. rewrite Heq_initShardMapping.
      eexists. apply lookup_replicate_2. word. }
    iPoseProof (big_sepS_intro_emp) as "H".
    iApply (big_sepS_mono with "H").
    { iIntros (x Hin) "_".
      rewrite Heq_initShardMapping. iExists _.
      iSplit.
      { iPureIntro. apply lookup_replicate_2.
        apply rangeSet_lookup in Hin; try word.
        { rewrite /uNSHARD in Hin. word. }
        { rewrite /uNSHARD. word. }
      }
      iLeft. eauto.
    }
  }
  iIntros "(Hloop_post&Hi)".
  wp_pures.
  replace  (ref (InjLV #0))%E with (NewMap uint64T) by auto.
  wp_apply (wp_NewMap).

  iIntros (mref) "Hmap".
  wp_storeField. wp_loadField.
  wp_apply (wp_MapInsert u64 _ _ _ (U64 65536) with "[$]").
  { eauto. }
  iIntros "Hmap".
  wp_pures.
  (* TODO: Pull this out to separate wp? *)
  wp_bind (MakeShardClerkSet #()).
  rewrite /MakeShardClerkSet.
  wp_lam.
  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT MemKVShardClerk)) by auto.
  wp_apply (map.wp_NewMap).
  iIntros (mref_set) "Hmap_set".
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (clset) "Hset".
  wp_storeField.
  iModIntro. iApply "HΦ".
  eauto.
Qed.
