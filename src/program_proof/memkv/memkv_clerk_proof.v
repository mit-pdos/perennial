From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export common_proof memkv_coord_clerk_proof memkv_shard_clerk_proof.

Section memkv_clerk_proof.

Context `{!heapG Σ, !rpcG Σ ShardReplyC, !rpcregG Σ, !kvMapG Σ}.

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

Lemma KVClerk__Get (ck:loc) (γ:gname) (key:u64) :
⊢ {{{ own_MemKVClerk ck γ }}}
  <<< ∀∀ v, kvptsto γ key v >>>
    MemKVClerk__Get #ck #key @ ⊤
  <<< kvptsto γ key v >>>
  {{{ val_sl q, RET slice_val val_sl;
      own_MemKVClerk ck γ ∗ typed_slice.is_slice_small val_sl byteT q%Qp v
  }}}.
Proof using Type*.
  iIntros "!#" (Φ) "Hown Hatomic".
  wp_lam.
  wp_pures.
  wp_apply wp_ref_of_zero.
  { done. }
  iIntros (rep_ptr) "Hrep".
  wp_pures.

  (* Weaken assumption for loop invariant *)
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
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet]").
  iIntros (??) "(HshardCk & %Hre & HcloseShardSet)".

  wp_pures.
  wp_apply (wp_MemKVShardClerk__Get _ _ γsh with "[Hatomic $HshardCk $Hrep]").
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
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iExists _, _, _, _. by iFrame.
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

Lemma KVClerk__Put (ck:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v:list u8):
⊢ {{{ own_MemKVClerk ck γ ∗ typed_slice.is_slice val_sl byteT 1%Qp v }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    MemKVClerk__Put #ck #key (slice_val val_sl) @ ⊤
  <<< kvptsto γ key v >>>
  {{{ RET #(); own_MemKVClerk ck γ }}}. (* FIXME: ownership of the slice is lost? *)
Proof using Type*.
  iIntros "!#" (Φ) "[Hown Hval_sl] Hatomic".
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
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet]").
  iIntros (??) "(HshardCk & %Hre & HcloseShardSet)".

  wp_pures.
  wp_apply (wp_MemKVShardClerk__Put _ _ γsh with "[Hatomic $Hval_sl $HshardCk]").
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
    iDestruct "HshardPutPost" as "(Hval_sl & HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    iApply "Hpost".
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iModIntro. iExists _, _, _, _. by iFrame.
  }
  {
    wp_loadField.
    iDestruct "HshardPutPost" as "(Hval_sl & HshardCk & [Hatomic|[%Hbad _]])"; last first.
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
    iFrame.
    iExists _,_,_,_. iFrame.
  }
Qed.

Lemma KVClerk__ConditionalPut (ck:loc) (γ:gname) (key:u64) (expv_sl newv_sl:Slice.t) (expv newv:list u8):
⊢ {{{ own_MemKVClerk ck γ ∗ typed_slice.is_slice expv_sl byteT 1%Qp expv ∗
      typed_slice.is_slice newv_sl byteT 1%Qp newv }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    MemKVClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) @ ⊤
  <<< kvptsto γ key (if bool_decide (expv = oldv) then newv else oldv) >>>
  {{{ RET #(bool_decide (expv = oldv)); own_MemKVClerk ck γ }}}. (* FIXME: ownership of the slices is lost? *)
Proof using Type*.
  iIntros "!#" (Φ) "(Hown & Hexpv_sl & Hnewv_sl) Hatomic".
  wp_lam.
  wp_pures.
  wp_apply (wp_ref_of_zero _ _ boolT).
  { done. }
  iIntros (succ_ptr) "Hsucc".
  wp_pures.
  (* Weaken assumption for loop invariant *)
  iAssert (∃ b:bool, succ_ptr ↦[boolT] #b)%I with "[Hsucc]" as "Hsucc".
  { iExists _. done. }

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
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet]").
  iIntros (??) "(HshardCk & %Hre & HcloseShardSet)".
  subst γ.

  wp_pures.
  wp_apply (wp_MemKVShardClerk__ConditionalPut _ _ γsh _ _ _ _ _ _ _ (λ b, own_MemKVClerk ck γsh.(kv_gn) -∗ Φ #b)%I
    with "[Hatomic $Hexpv_sl $Hnewv_sl $HshardCk Hsucc]").
  {
    rewrite /zero_val /=. iFrame.
  }
  iIntros (e) "HshardCondPutPost".
  wp_pures.
  wp_if_destruct.
  {
    iRight.
    iModIntro.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HshardCondPutPost" as "(Hexpv_sl & Hnewv_sl & HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    iDestruct "Hpost" as (succ) "(Hsucc & HΦ)".
    wp_load.
    iApply "HΦ". iModIntro.
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iExists _, _, _, _. by iFrame.
  }
  {
    wp_loadField.
    iDestruct "HshardCondPutPost" as "(Hexpv_sl & Hnewv_sl & HshardCk & [Hatomic|[%Hbad _]])"; last first.
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
    iDestruct "Hatomic" as "(_ & $ & Hsucc)".
    iFrame.
    iExists _,_,_,_; iFrame.
  }
Qed.

End memkv_clerk_proof.
