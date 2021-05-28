From Perennial.Helpers Require Import range_set.
From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions common_proof.

Section memkv_shard_make_proof.

Context `{!heapG Σ, rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_MakeMemKVShardServer (b : bool) γ :
  {{{
       "#His_srv" ∷ is_RPCServer γ.(rpc_gn) ∗
       "HRPCserver_own" ∷ RPCServer_own_ghost γ.(rpc_gn) ∅ ∅ ∗
       "HghostShards" ∷ (if b then [∗ set] sid ∈ rangeSet 0 uNSHARD, own_shard γ.(kv_gn) sid ∅ else True) ∗
       "Hcids" ∷ [∗ set] cid ∈ (fin_to_set u64), RPCClient_own_ghost γ.(rpc_gn) cid 1
  }}}
    MakeMemKVShardServer #b
  {{{
       s, RET #s; is_MemKVShardServer s γ
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.  Opaque slice.T. }
  iIntros (srv) "srv".
  wp_pures.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  iDestruct (struct_fields_split with "srv") as "srv". iNamed "srv".
  wp_storeField.
  replace  (ref (InjLV (#0, (zero_val (slice.T byteT), (#false, #())))))%E
    with (NewMap (struct.t ShardReply)) by naive_solver.
  wp_apply (map.wp_NewMap).
  iIntros (lastReply_ptr) "HlastReplyMap".
  wp_storeField.
  replace (ref (InjLV #0))%E with (NewMap uint64T) by naive_solver.
  wp_apply (wp_NewMap).
  iIntros (lastSeq_ptr) "HlastSeqMap".
  wp_storeField.
  wp_apply (typed_slice.wp_NewSlice).
  iIntros (shardMap_sl) "HshardMap_sl".
  Transparent slice.T. wp_storeField. Opaque slice.T.
  wp_apply (wp_new_slice).
  { econstructor. }
  iIntros (kvss_sl) "Hkvss_sl".
  Transparent slice.T. wp_storeField. Opaque slice.T.
  replace (ref (InjLV #null))%E with ((NewMap (struct.ptrT MemKVShardClerk))) by auto.
  remember (replicate (int.nat 65536) IntoVal_def) as initShardMapping eqn:Heq_initShardMapping.
  remember (replicate (int.nat 65536) (@zero_val grove_op grove_ty KvMap)) as init_kvs_ptrs eqn:Heq_init_kvs_ptrs.
  wp_apply (wp_NewMap).
  iIntros (peers_ptr) "HpeersMap".
  wp_storeField.
  wp_apply (wp_ref_to).
  { repeat econstructor. }
  iIntros (iptr) "Hi".
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ shardMapping kvs_ptrs,
  "%Hlen_shardMapping" ∷ ⌜ Z.of_nat (length shardMapping) = uNSHARD ⌝ ∗
  "%Hlen_kvs_ptrs" ∷ ⌜ Z.of_nat (length kvs_ptrs) = uNSHARD ⌝ ∗
  "%HshardMapping_dom" ∷ ⌜ (∀ i : u64, int.Z i < int.Z uNSHARD → is_Some (shardMapping !! int.nat i)) ⌝ ∗
  "%Hkvss_dom" ∷ ⌜ (∀ i : u64, int.Z i < int.Z uNSHARD →
                               is_Some ((fmap (λ x : loc, #x) kvs_ptrs) !! int.nat i)) ⌝ ∗
  "HghostShards" ∷ (if b then ([∗ set] sid ∈ rangeSet (int.Z i) (uNSHARD - int.Z i), own_shard γ.(kv_gn) sid ∅)
                   else True) ∗
  "kvss" ∷ srv ↦[MemKVShardServer :: "kvss"] (slice_val kvss_sl) ∗
  "Hkvss_sl" ∷ slice.is_slice kvss_sl (mapT (slice.T byteT)) 1%Qp (fmap (λ x:loc, #x) kvs_ptrs) ∗
  "shardMap" ∷ srv ↦[MemKVShardServer :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷  typed_slice.is_slice shardMap_sl boolT 1 shardMapping ∗
  "HownShards" ∷ ([∗ set] sid ∈ (fin_to_set u64),
                  ⌜(shardMapping !! (int.nat sid)) ≠ Some true⌝ ∨
                  (∃ (kvs_ptr:loc) (m:gmap u64 (list u8)) (mv:gmap u64 goose_lang.val),
                      own_shard γ.(kv_gn) sid m ∗ (* own shard *)
                      ⌜kvs_ptrs !! (int.nat sid) = Some kvs_ptr⌝ ∗
                      map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
                      ([∗ set] k ∈ (fin_to_set u64),
                       ⌜shardOfC k ≠ sid⌝ ∨ (∃ q vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice_small vsl byteT q (default [] (m !! k))))
                  )))%I with "[] [$Hi HshardMap_sl shardMap HghostShards kvss Hkvss_sl]").
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
    wp_apply (typed_slice.wp_SliceSet with "[$HshardMap_sl]").
    { eauto. }
    iIntros "HshardMap_sl".
    iDestruct ("HshardMap_sl_close" with "[$HshardMap_sl]") as "HshardMap_sl".
    wp_pures.
    wp_if_destruct.
    {
      wp_pures.
      replace (ref (InjLV (#null, #0, #0)))%E with ((NewMap (slice.T byteT))) by auto.
      wp_apply (map.wp_NewMap). iIntros (mv) "Hmv".
      wp_apply (wp_LoadAt with "[$Hi]").
      iIntros "Hi".
      wp_loadField.
      iDestruct (is_slice_small_acc with "Hkvss_sl") as "(Hkvss_sl&Hkvss_sl_close)".
      wp_apply (wp_SliceSet with "[$Hkvss_sl]").
      { iPureIntro; split; eauto. }
      iIntros "Hkvss_sl".
      iDestruct ("Hkvss_sl_close" with "[$Hkvss_sl]") as "Hkvss_sl".
      (*
        edestruct (Hkvss_dom) as (?&Heq); first eassumption. eexists.
        Search lookup fmap. eapply lookup_fmap_Some; eauto. } *)
      wp_pures. iModIntro. iApply "HΦ".
      { iFrame. iExists _, (<[int.nat i := mv]>kvs_ptrs). iFrame.
        rewrite ?insert_length.
        do 2 (iSplit; first done).
        iSplit.
        { iPureIntro. intros.
          destruct (decide (int.nat i0 = int.nat i)) as [->|Hneq].
          { eexists. apply list_lookup_insert. eapply lookup_lt_is_Some_1; eauto. }
          rewrite list_lookup_insert_ne; auto.
        }
        assert ((int.nat i < length kvs_ptrs)%nat).
        { erewrite <-fmap_length. eapply lookup_lt_is_Some_1; eauto. }
        iSplit.
        { iPureIntro. intros.
          rewrite list_lookup_fmap.
          destruct (decide (int.nat i0 = int.nat i)) as [->|Hneq].
          { rewrite fmap_is_Some. eexists. apply list_lookup_insert; eauto. }
          rewrite list_lookup_insert_ne; auto.
          rewrite -list_lookup_fmap. eauto. }
        rewrite rangeSet_first; last first.
        { rewrite /uNSHARD. word. }
        iDestruct (big_sepS_union with "HghostShards") as "(Hgi&HghostShards)".
        { apply rangeSet_first_disjoint; rewrite /uNSHARD; word. }
        iSplitL "HghostShards".
        { cut (rangeSet (int.Z i + 1) (uNSHARD - int.Z i - 1) =
               rangeSet (int.Z (word.add i 1)) (uNSHARD - int.Z (word.add i 1))).
          { intros ->. eauto. }
          f_equal; word. }
        iSplitL "Hkvss_sl".
        { rewrite list_fmap_insert. eauto. }
        assert (i ∈ (fin_to_set u64 : gset u64)).
        { apply elem_of_fin_to_set. }
        assert (fin_to_set u64 = {[i]} ∪ ((fin_to_set u64 : gset u64) ∖ {[i]})) as Heq_diff.
        { apply union_difference_singleton_L; eauto. }
        iEval (rewrite {2}Heq_diff) in "HownShards".
        iEval (rewrite {2}Heq_diff).
        iApply big_sepS_union.
        { set_solver. }
        iDestruct (big_sepS_union with "HownShards") as "(Hi&HownShards)".
        { set_solver. }
        iSplitL "Hi Hmv Hgi".
        { rewrite ?big_sepS_singleton.
          iRight. iExists _, ∅, _. iFrame. iSplitL "Hgi".
          { iExactEq "Hgi". f_equal. word. }
          iSplit.
          { iPureIntro. rewrite list_lookup_insert; eauto. }
          iApply big_sepS_intro.
          iIntros "!#" (??).
          destruct (decide (shardOfC x = i)); last by eauto.
          { iRight. iExists 1%Qp, _. rewrite ?lookup_empty //=.
            iSplit; first eauto.
            iApply (typed_slice.is_slice_to_small (V:=u8)).
            iApply typed_slice.is_slice_zero. }
        }
        iApply (big_sepS_mono with "HownShards").
        { iIntros (??) "H".
          assert (int.nat i ≠ int.nat x).
          { cut (i ≠ x).
            { intros. intros Heq. apply Z2Nat.inj in Heq; try word.
               apply int_Z_inj in Heq; eauto with *.
            }
            set_solver. }
          rewrite ?list_lookup_insert_ne //.
        }
      }
    }
    {
      wp_pures. iModIntro. iApply "HΦ".
      { iFrame. iExists _, kvs_ptrs. iFrame.
        iSplit.
        { iPureIntro. rewrite insert_length //. }
        iSplit.
        { eauto. }
        iSplit.
        { iPureIntro. intros.
          destruct (decide (int.nat i0 = int.nat i)) as [->|Hneq].
          { eexists. apply list_lookup_insert. eapply lookup_lt_is_Some_1; eauto. }
          rewrite list_lookup_insert_ne; auto.
        }
        assert ((int.nat i < length kvs_ptrs)%nat).
        { erewrite <-fmap_length. eapply lookup_lt_is_Some_1; eauto. }
        iSplit.
        { iPureIntro. eauto. }
        assert (i ∈ (fin_to_set u64 : gset u64)).
        { apply elem_of_fin_to_set. }
        assert (fin_to_set u64 = {[i]} ∪ ((fin_to_set u64 : gset u64) ∖ {[i]})) as Heq_diff.
        { apply union_difference_singleton_L; eauto. }
        iEval (rewrite {2}Heq_diff) in "HownShards".
        iEval (rewrite {2}Heq_diff).
        iApply big_sepS_union.
        { set_solver. }
        iDestruct (big_sepS_union with "HownShards") as "(Hi&HownShards)".
        { set_solver. }
        iSplitL "Hi".
        { rewrite ?big_sepS_singleton.
          iLeft. rewrite list_lookup_insert //. eapply lookup_lt_is_Some_1; eauto. }
        iApply (big_sepS_mono with "HownShards").
        { iIntros (??) "H".
          assert (int.nat i ≠ int.nat x).
          { cut (i ≠ x).
            { intros. intros Heq. apply Z2Nat.inj in Heq; try word.
               apply int_Z_inj in Heq; eauto with *.
            }
            set_solver. }
          rewrite ?list_lookup_insert_ne //.
        }
      }
    }
  }
  {
    iExists initShardMapping.
    iExists (replicate (int.nat 65536) null).
    iSplit.
    { iPureIntro. rewrite Heq_initShardMapping replicate_length /uNSHARD. word. }
    iSplit.
    { iPureIntro. rewrite replicate_length /uNSHARD. word. }
    iSplit.
    { iPureIntro. rewrite /uNSHARD. intros i Hlt. rewrite Heq_initShardMapping.
      eexists. apply lookup_replicate_2. word. }
    iSplit.
    { iPureIntro. rewrite /uNSHARD. intros i Hlt.
      rewrite list_lookup_fmap fmap_is_Some.
      eexists. apply lookup_replicate_2. word. }
    iFrame.
    iSplitL "Hkvss_sl".
    { rewrite /named. iExactEq "Hkvss_sl". f_equal.
      rewrite Heq_init_kvs_ptrs fmap_replicate. f_equal. }
    iApply big_sepS_intro.
    iIntros "!#" (x Hin). iLeft. iPureIntro. intros Hfalse.
    rewrite Heq_initShardMapping in Hfalse.
    apply lookup_replicate_1 in Hfalse as (Hbad&?). rewrite //= in Hbad.
  }
  iIntros "(Hloop_post&Hi)".
  iMod (alloc_lock memKVN _ lk (own_MemKVShardServer srv γ) with "[$] [-mu HΦ]").
  {
    iNext. iNamed "Hloop_post".
    iExists _, _, _, _, _, _, _, _.
    iExists _, _, _, _.
    iFrame "lastReply lastSeq nextCID shardMap kvss peers".
    iFrame.
    iSplit.
    { iPureIntro. rewrite ?dom_empty_L //. }
    iSplitL "".
    { rewrite big_sepM2_empty //. }
    iSplit; first done.
    iSplit; first done.
    rewrite big_sepM_empty.
    iSplit; first done.
    iApply (big_sepS_mono with "Hcids"); by eauto.
  }
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _|].
  wp_pures. iApply "HΦ". iModIntro.
  iExists _. iFrame "# ∗".
Qed.

End memkv_shard_make_proof.
