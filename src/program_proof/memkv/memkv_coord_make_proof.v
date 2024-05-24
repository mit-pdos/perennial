From Perennial.Helpers Require Import range_set.
From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.

From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_coord_definitions common_proof.

#[local] Set Universe Polymorphism.

Section memkv_coord_make_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_MakeKVCoordServer (initserver : u64) (γ : memkv_coord_names) γinit :
  {{{
       "%Hinitserver_gnames" ∷ ⌜γinit.(kv_gn) = γ.(coord_kv_gn)⌝ ∗
       "#Hinit_is_shard_server" ∷ is_shard_server initserver γinit
  }}}
    MakeKVCoordServer #initserver
  {{{
       s, RET #s; is_KVCoordServer s γ
  }}}.
Proof.
  iIntros (Φ) "H HΦ".
  iNamed "H".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (s) "srv".
  wp_pures.
  wp_apply (wp_new_free_lock). iIntros (lk) "Hfree".
  iDestruct (struct_fields_split with "srv") as "srv". iNamed "srv".
  wp_storeField.
  wp_apply (typed_slice.wp_NewSlice (V:=u64)).
  iIntros (shardMap_sl) "HshardMap_sl".
  wp_storeField.
  remember (replicate (uint.nat 65536) (IntoVal_def _)) as initShardMapping eqn:Heq_initShardMapping.
  wp_apply (wp_ref_to); first val_ty.
  iIntros (iptr) "Hi".
  wp_pures.
  wp_pures.
  wp_apply (wp_forUpto (λ i, ∃ shardMapping,
  "%Hlen_shardMapping" ∷ ⌜ Z.of_nat (length shardMapping) = uNSHARD ⌝ ∗
  "%HshardMapping_dom" ∷ ⌜ (∀ i : u64, uint.Z i < uint.Z uNSHARD → is_Some (shardMapping !! uint.nat i)) ⌝ ∗
  "shardMap" ∷ s ↦[KVCoord :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ @typed_slice.own_slice grove_op grove_model grove_interp Σ _ grove_ty u64
                     (@u64_IntoVal grove_op) shardMap_sl HostName (DfracOwn 1) shardMapping ∗
  "HownShards" ∷ ([∗ set] sid ∈ rangeSet 0 uNSHARD, ∃ (hid : u64),
                  ⌜ shardMapping !! uint.nat sid = Some hid ⌝ ∗
                  (⌜ hid = 0 ∧ uint.nat i ≤ uint.nat sid ⌝  ∨ ∃ hγ, ⌜ hγ.(kv_gn) = γ.(coord_kv_gn) ⌝ ∗ is_shard_server hid hγ)
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
    iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "(HshardMap_sl&HshardMap_sl_close)".
    wp_apply (typed_slice.wp_SliceSet (V:=u64) with "[$HshardMap_sl]").
    { eauto. }
    iIntros "HshardMap_sl".
    iDestruct ("HshardMap_sl_close" with "[$HshardMap_sl]") as "HshardMap_sl".
    wp_pures. iModIntro. iApply "HΦ".
    remember uNSHARD as uNSHARD' eqn:Heq_uNSHARD.
    { iFrame.
      iSplit.
      { iPureIntro. rewrite insert_length //. }
      iSplit.
      { iPureIntro. intros.
        destruct (decide (uint.nat i0 = uint.nat i)) as [->|Hneq].
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
        assert (uint.nat i ≠ uint.nat x).
        { cut (i ≠ x).
          { intros. intros Heq. apply Z2Nat.inj in Heq; try word.
             apply int_Z_inj in Heq; eauto with *.
          }
          move:Hin. set_solver+. }
        rewrite ?list_lookup_insert_ne //.
        iDestruct "H" as (hid ?) "H". iExists hid; iSplit; first eauto.
        iDestruct "H" as "[%Hzero|H2]".
        { iLeft. iPureIntro. destruct Hzero as (?&?); split; first auto.
          word_cleanup. }
        { eauto. }
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
    iApply big_sepS_intro.
    iIntros "!#" (x Hin).
    rewrite Heq_initShardMapping. iExists _.
    iSplit.
    { iPureIntro. apply lookup_replicate_2.
      apply rangeSet_lookup in Hin; try word.
      { rewrite /uNSHARD in Hin. word. }
      { rewrite /uNSHARD. word. }
    }
    iLeft. iPureIntro; split; eauto. word.
  }
  iIntros "(Hloop_post&Hi)".
  wp_pures.
  wp_apply (wp_NewMap u64).

  iIntros (mref) "Hmap".
  wp_storeField. wp_loadField.
  wp_apply (wp_MapInsert _ u64 (W64 65536) with "[$]").
  { eauto. }
  iIntros "Hmap".
  wp_pures.
  wp_apply wp_MakeConnMan.
  iIntros (c) "Hc_own".
  (* TODO: Pull this out to separate wp? it is called at least twice *)
  wp_bind (MakeShardClerkSet _).
  wp_lam.
  wp_apply (wp_NewMap u64).
  iIntros (mref_set) "Hmap_set".
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (clset) "Hset".
  wp_storeField.
  iMod (alloc_lock memKVN _ lk (own_KVCoordServer s γ.(coord_kv_gn)) with "[$Hfree] [-mu HΦ]").
  {
    iNext.
    iNamed "Hloop_post".
    remember uNSHARD as uNSHARD' eqn:Heq_uNSHARD.
    iExists _, _, _, _, _. iFrame.
    iSplit.
    { iPureIntro. congruence. }
    iSplit.
    { iPureIntro. intros i Hlt.
      eapply HshardMapping_dom. rewrite Heq_uNSHARD. eauto. }
    iSplitL "HownShards".
    {
      rewrite /all_are_shard_servers. iIntros (sid host Hlookup).
      iDestruct (big_sepS_elem_of _ _ (W64 sid) with "HownShards") as "H".
      { apply rangeSet_lookup; try word.
        - rewrite Heq_uNSHARD /uNSHARD. lia.
        - split.
          * apply encoding.unsigned_64_nonneg.
          * apply lookup_lt_Some in Hlookup.
            rewrite Z_u64.
            ** lia.
            ** split; try lia. rewrite Heq_uNSHARD /uNSHARD in Hlen_shardMapping. lia.
      }
      iDestruct "H" as (? Hlookup2) "[%Hbad|H]".
      { destruct Hbad as (_&Hle). exfalso.
        apply lookup_lt_Some in Hlookup.
        rewrite Heq_uNSHARD /uNSHARD in Hlen_shardMapping.
        word_cleanup.
        rewrite -Hlen_shardMapping in Hle.
        rewrite Z_u64 ?Nat2Z.id in Hle; word_cleanup.
      }
      iDestruct "H" as (??) "H". iExists _.
      assert (host = hid) as ->.
      {
        assert (uint.nat (W64 (Z.of_nat sid)) = sid) as Hcoerce.
        { word_cleanup.
          rewrite wrap_small; first lia.
          { split.
          * lia.
          *  apply lookup_lt_Some in Hlookup.
            rewrite Heq_uNSHARD /uNSHARD in Hlen_shardMapping. lia.
          }
        }
        { rewrite Hcoerce in Hlookup2. congruence. }
      }
      iFrame. eauto.
    }
    iDestruct (struct_fields_split with "Hset") as "Hset". iNamed "Hset".
    iFrame. rewrite big_sepM_empty. eauto.
  }
  unshelve (iMod (readonly_alloc_1 with "mu") as "#mu"); [| apply _ |].
  iModIntro. iApply "HΦ". iExists _. iFrame "∗#".
Qed.

End memkv_coord_make_proof.
