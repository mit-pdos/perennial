From Perennial.program_proof Require Import disk_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export rpc_axioms common_proof memkv_coord_clerk_proof memkv_shard_clerk_proof.

Section memkv_clerk_proof.

Context `{!heapG Σ, rpcG Σ GetReplyC, kvMapG Σ}.

Definition own_MemKVClerk (ck:loc) (γ:gname) : iProp Σ :=
  ∃ (s coordCk:loc) shardMap_sl (shardMapping:list u64),
  "HshardClerks" ∷ ck ↦[MemKVClerk :: "shardClerks"] #s ∗
  "HshardClerksSet" ∷ own_ShardClerkSet s γ ∗
  "HcoordCk" ∷ ck ↦[MemKVClerk :: "coordCk"] #coordCk ∗
  "HcoordCk_own" ∷ own_MemKVCoordClerk coordCk ∗
  "HshardMap" ∷ ck ↦[MemKVClerk :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl uint64T 1%Qp shardMapping ∗
  "%HshardMap_length" ∷ ⌜length shardMapping = uNSHARD⌝
.

Lemma KVClerk__Get Eo Ei (ck:loc) (γ:gname) (key:u64) :
  ∀ Φ,
  own_MemKVClerk ck γ -∗
  (|={Eo,Ei}=> (∃ v, kvptsto γ key v ∗ (kvptsto γ key v ={Ei,Eo}=∗ (∀ val_sl q, typed_slice.is_slice_small val_sl byteT q%Qp v -∗ (Φ (slice_val val_sl)))))) -∗
    WP MemKVClerk__Get #ck #key {{ Φ }}
.
Proof using Type*.
  iIntros (Φ) "Hown Hatomic".
  wp_lam.
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.

  iAssert (∃ rep_sl, rep_ptr ↦[slice.T byteT] (slice_val rep_sl) )%I with "[Hrep]" as "Hrep".
  {
    rewrite zero_slice_val.
    iExists _; iFrame.
  }

  wp_forBreak.
  wp_pures.

  wp_apply (wp_shardOf_bound).
  iIntros (sid HsidLe).
  wp_pures.

  iNamed "Hown".
  wp_loadField.
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  rewrite -HshardMap_length in HsidLe.
  eapply list_lookup_lt in HsidLe.
  destruct HsidLe as [hostID HsidLe].
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.
  wp_apply (wp_ShardClerkSet__getClerk with "[$HshardClerksSet]").
  iIntros (??) "(HshardCk & %Hre & HcloseShardSet)".

  wp_pures.
  wp_apply (wp_MemKVShardClerk__Get Eo Ei γsh with "[Hatomic $HshardCk $Hrep]").
  {
    rewrite Hre.
    iFrame "Hatomic".
  }
  iIntros (e) "HshardGetPost".
  wp_pures.
  wp_if_destruct.
  {
    iRight.
    iModIntro.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HshardGetPost" as "(HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    iNamed "Hpost".
    iDestruct "Hpost" as "(Hrep & Hval_sl & HΦ)".
    wp_load.
    iModIntro.
    iApply "HΦ".
    iFrame.
  }
  {
    wp_loadField.
    iDestruct "HshardGetPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_MemKVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "[HcoordCk_own HshardMap_sl]".
    wp_apply (wp_storeField with "HshardMap").
    { apply slice_val_ty. }
    iIntros "HshardMap".
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    rewrite Hre.
    iDestruct "Hatomic" as "[_ $]".
    iExists _,_,_,_; iFrame.
  }
Qed.

Lemma KVClerk__Put Eo Ei (ck:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v:list u8):
  ∀ Φ,
  own_MemKVClerk ck γ -∗
  typed_slice.is_slice val_sl byteT 1%Qp v -∗
  (|={Eo,Ei}=> (∃ oldv, kvptsto γ key oldv ∗ (kvptsto γ key v ={Ei,Eo}=∗ (Φ #())))) -∗
    WP MemKVClerk__Put #ck #key (slice_val val_sl) {{ Φ }}
.
Proof using Type*.
  iIntros (Φ) "Hown Hval_sl Hatomic".
  wp_lam.
  wp_pures.

  wp_forBreak.
  wp_pures.

  wp_apply (wp_shardOf_bound).
  iIntros (sid HsidLe).
  wp_pures.

  iNamed "Hown".
  wp_loadField.
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  rewrite -HshardMap_length in HsidLe.
  eapply list_lookup_lt in HsidLe.
  destruct HsidLe as [hostID HsidLe].
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.
  wp_apply (wp_ShardClerkSet__getClerk with "[$HshardClerksSet]").
  iIntros (??) "(HshardCk & %Hre & HcloseShardSet)".

  wp_pures.
  wp_apply (wp_MemKVShardClerk__Put Eo Ei γsh with "[Hatomic $Hval_sl $HshardCk]").
  {
    rewrite Hre.
    iFrame "Hatomic".
  }
  iIntros (e) "HshardPutPost".
  wp_pures.
  wp_if_destruct.
  {
    iRight.
    iModIntro.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HshardPutPost" as "(HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    by iFrame.
  }
  {
    wp_loadField.
    iDestruct "HshardPutPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_MemKVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "[HcoordCk_own HshardMap_sl]".
    wp_apply (wp_storeField with "HshardMap").
    { apply slice_val_ty. }
    iIntros "HshardMap".
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    rewrite Hre.
    iDestruct "Hatomic" as "[_ $]".
    iSplitR ""; last admit. (* TODO: need to get back ownership of value slice from ShardClerk, which requires getting back ownership from encodePutRequest *)
    iExists _,_,_,_; iFrame.
  }
Admitted.

End memkv_clerk_proof.
