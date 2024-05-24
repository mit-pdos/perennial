From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions memkv_marshal_install_shard_proof.

#[local] Set Universe Polymorphism.

Section memkv_install_shard_proof.

Context `{!heapGS Σ, erpcG Σ, urpcregG Σ, kvMapG Σ}.

Lemma wp_InstallShardRPC (s args_ptr:loc) args γ :
  is_KVShardServer s γ -∗
  {{{
       own_InstallShardRequest args_ptr args ∗
       ⌜uint.nat args.(IR_Sid) < uNSHARD⌝ ∗
       (own_shard γ.(kv_gn) args.(IR_Sid) args.(IR_Kvs))
  }}}
    KVShardServer__InstallShardRPC #s #args_ptr
  {{{
       RET #(); True
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hargs & %HsidLe & Hpre)".
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

  (* update shardMap to have sid ↦ true *)
  wp_pures.
  wp_loadField.
  wp_loadField.
  iDestruct (typed_slice.own_slice_small_acc with "HshardMap_sl") as "[HshardMap_small HshardMap_sl]".
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
  iDestruct (slice.own_slice_split with "Hkvss_sl") as "[Hkvss_small Hkvss_sl]".
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

  wp_loadField.
  wp_apply (release_spec with "[-HΦ]").
  {
    iFrame "HmuInv Hlocked".
    iNext.
    iExists _,_,_,_,_,_.
    iFrame.
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
    assert (uint.nat x ≠ uint.nat args.(IR_Sid)).
    {
      destruct (bool_decide (uint.Z x = uint.Z args.(IR_Sid))) as [|] eqn:X.
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
