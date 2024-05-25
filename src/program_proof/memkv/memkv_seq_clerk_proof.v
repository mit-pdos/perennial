From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export common_proof memkv_coord_definitions memkv_coord_clerk_proof memkv_shard_clerk_proof.

Section memkv_clerk_proof.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !erpcG Σ, !urpcregG Σ, !kvMapG Σ}.

Definition own_SeqKVClerk (ck:loc) (γ:gname) : iProp Σ :=
  ∃ (s coordCk:loc) shardMap_sl (shardMapping:list u64),
  "HshardClerks" ∷ ck ↦[SeqKVClerk :: "shardClerks"] #s ∗
  "HshardClerksSet" ∷ own_ShardClerkSet s γ ∗
  "HcoordCk" ∷ ck ↦[SeqKVClerk :: "coordCk"] #coordCk ∗
  "HcoordCk_own" ∷ own_KVCoordClerk coordCk γ ∗
  "HshardMap" ∷ ck ↦[SeqKVClerk :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ own_slice shardMap_sl uint64T (DfracOwn 1) shardMapping ∗
  "%HshardMap_length" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
  "#HshardServers" ∷ all_are_shard_servers shardMapping γ
.

Lemma wp_MakeSeqKVClerk (coord:u64) cm γ :
  {{{
       is_coord_server coord γ ∗ is_ConnMan cm
  }}}
    MakeSeqKVClerk #coord #cm
  {{{
       (ck:loc), RET #ck; own_SeqKVClerk ck γ.(coord_kv_gn)
  }}}
.
Proof.
  iIntros (Φ) "[#Hcoord #Hcm] HΦ".
  wp_lam.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (cck) "Hcck".
  wp_pures.
  wp_apply wp_allocStruct; first val_ty.
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  iDestruct (struct_fields_split with "Hcck") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_bind (MakeShardClerkSet _).
  wp_lam.
  wp_apply (wp_NewMap).
  iIntros (mref_set) "Hmap_set".
  wp_apply wp_allocStruct; first val_ty.
  iIntros (clset) "Hset".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_KVCoordClerk__GetShardMap with "[c host]").
  { rewrite /own_KVCoordClerk. iExists _, _, _. iFrame "c host Hcm".
    iSplit; last first.
    { iExact "Hcoord". }
    done.
  }
  iIntros (shardMap_sl shardMapping) "(Hcck & HshardMap_sl & %Hlen & #Hall_are_shard_servers)".
  wp_storeField.
  iModIntro. iApply "HΦ".
  iExists _, _, _, _. iFrame.
  iFrame "% #".
  iDestruct (struct_fields_split with "Hset") as "HH".
  iNamed "HH". iFrame.
  rewrite big_sepM_empty; done.
Qed.

Lemma wp_SeqKVClerk__Get (ck:loc) (γ:gname) (key:u64) :
⊢ {{{ own_SeqKVClerk ck γ }}}
  <<< ∀∀ v, kvptsto γ key v >>>
    SeqKVClerk__Get #ck #key @ ∅
  <<< kvptsto γ key v >>>
  {{{ val_sl q, RET slice_val val_sl;
      own_SeqKVClerk ck γ ∗ own_slice_small val_sl byteT q%Qp v
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
  iDestruct (own_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  assert (uint.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (uint.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".

  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet]").
  { iFrame "HH". }
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_KVShardClerk__Get with "[Hatomic $HshardCk $Hrep]").
  {
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
    iDestruct "Hpost" as "(Hrep & #Hval_sl & HΦ)".
    wp_load.
    iModIntro.
    iApply "HΦ".
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    by iFrame "∗#".
  }
  {
    wp_loadField.
    iDestruct "HshardGetPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_KVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_storeField.
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "[_ $]".
    iExists _,_,_,_; by iFrame "∗#".
  }
Qed.

(* Sequential spec *)
Lemma wp_SeqKVClerk__Get_seq (ck:loc) (γ:gname) (key:u64) (v:list u8) :
  {{{ own_SeqKVClerk ck γ ∗ kvptsto γ key v }}}
    SeqKVClerk__Get #ck #key @ ⊤
  {{{ val_sl q, RET slice_val val_sl;
      own_SeqKVClerk ck γ ∗ kvptsto γ key v ∗ own_slice_small val_sl byteT q%Qp v
  }}}.
Proof using Type*.
  iIntros (Φ) "(Hclerk & Hkey) HΦ".
  iApply (wp_SeqKVClerk__Get with "Hclerk").
  iApply fupd_mask_intro; first done. iNext.
  iIntros "Hclose". iExists _. iFrame "Hkey".
  iIntros "Hkey". iMod "Hclose" as "_". iModIntro.
  iIntros (??) "[Hclerk Hsl]". iApply "HΦ". iFrame.
Qed.

Lemma wp_SeqKVClerk__Put (ck:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v:list u8):
⊢ {{{ own_SeqKVClerk ck γ ∗ own_slice_small val_sl byteT DfracDiscarded v }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    SeqKVClerk__Put #ck #key (slice_val val_sl) @ ∅
  <<< kvptsto γ key v >>>
  {{{ RET #(); own_SeqKVClerk ck γ }}}.
Proof using Type*.
  iIntros "!#" (Φ) "[Hown #Hval_sl] Hatomic".
  wp_lam.
  wp_pures.

  wp_forBreak.
  wp_pures.

  wp_apply (wp_shardOf_bound).
  iIntros (sid HsidLe).
  wp_pures.

  iNamed "Hown".
  wp_loadField.
  iDestruct (own_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  assert (uint.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (uint.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet $HH]").
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_KVShardClerk__Put with "[Hatomic $Hval_sl $HshardCk]").
  {
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
    iApply "Hpost".
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iModIntro. iExists _, _, _, _. by iFrame "∗#".
  }
  {
    wp_loadField.
    iDestruct "HshardPutPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_KVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_storeField.
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "[_ $]".
    by iFrame "∗#".
  }
Qed.

Lemma wp_SeqKVClerk__ConditionalPut (ck:loc) (γ:gname) (key:u64) (expv_sl newv_sl:Slice.t) (expv newv:list u8):
⊢ {{{ own_SeqKVClerk ck γ ∗
      own_slice_small expv_sl byteT DfracDiscarded expv ∗
      own_slice_small newv_sl byteT DfracDiscarded newv }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    SeqKVClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) @ ∅
  <<< kvptsto γ key (if bool_decide (expv = oldv) then newv else oldv) >>>
  {{{ RET #(bool_decide (expv = oldv));
      own_SeqKVClerk ck γ }}}.
Proof using Type*.
  iIntros "!#" (Φ) "(Hown & #Hexpv_sl & #Hnewv_sl) Hatomic".
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
  iDestruct (own_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  assert (uint.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (uint.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet $HH]").
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_KVShardClerk__ConditionalPut _ _ _ _ _ _ _ _ (λ b, own_SeqKVClerk ck γ -∗ Φ #b)%I
    with "[Hatomic $HshardCk Hsucc]").
  { eauto with iFrame. }
  iIntros (e) "HshardCondPutPost".
  wp_pures.
  wp_if_destruct.
  {
    iRight.
    iModIntro.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HshardCondPutPost" as "(HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    iDestruct "Hpost" as (succ) "(Hsucc & HΦ)".
    wp_load.
    iApply "HΦ". iModIntro.
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    by iFrame "∗#".
  }
  {
    wp_loadField.
    iDestruct "HshardCondPutPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_KVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_storeField.
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "(_ & $ & Hsucc)".
    by iFrame "∗#".
  }
Qed.

Lemma wp_SeqKVClerk__Add (ck:loc) γkv γ (dst : u64) :
  {{{
       own_SeqKVClerk ck γkv ∗
       is_shard_server dst γ ∗
       ⌜γ.(kv_gn) = γkv⌝
  }}}
    SeqKVClerk__Add #ck #dst
  {{{RET #(); own_SeqKVClerk ck γkv }}}
.
Proof.
  iIntros (Φ) "(Hown&#His_shard&%) HΦ".
  wp_lam.
  wp_pures.
  iNamed "Hown".
  wp_loadField.
  wp_apply (wp_KVCoordClerk__AddShardServer with "[$HcoordCk_own $His_shard]"); eauto.
  iIntros "HcoordCk_own".
  wp_pures. iModIntro. iApply "HΦ".
  rewrite /own_SeqKVClerk.
  iExists _, _, _, _. iFrame. eauto.
Qed.

End memkv_clerk_proof.
