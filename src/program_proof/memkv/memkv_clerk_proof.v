From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_logic Require Import atomic_fupd.
From Perennial.program_proof.memkv Require Export common_proof memkv_coord_definitions memkv_coord_clerk_proof memkv_shard_clerk_proof.

Section memkv_clerk_proof.

Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), !rpcG Σ ShardReplyC, !rpcregG Σ, !kvMapG Σ}.

Definition own_MemKVClerk (ck:loc) (γ:gname) : iProp Σ :=
  ∃ (s coordCk:loc) shardMap_sl (shardMapping:list u64),
  "HshardClerks" ∷ ck ↦[MemKVClerk :: "shardClerks"] #s ∗
  "HshardClerksSet" ∷ own_ShardClerkSet s γ ∗
  "HcoordCk" ∷ ck ↦[MemKVClerk :: "coordCk"] #coordCk ∗
  "HcoordCk_own" ∷ own_MemKVCoordClerk coordCk γ ∗
  "HshardMap" ∷ ck ↦[MemKVClerk :: "shardMap"] (slice_val shardMap_sl) ∗
  "HshardMap_sl" ∷ typed_slice.is_slice shardMap_sl uint64T 1%Qp shardMapping ∗
  "%HshardMap_length" ∷ ⌜Z.of_nat (length shardMapping) = uNSHARD⌝ ∗
  "#HshardServers" ∷ all_are_shard_servers shardMapping γ
.

Lemma wp_MakeMemKVClerk (coord:u64) γ :
  {{{
       is_coord_server coord γ
  }}}
    MakeMemKVClerk #coord
  {{{
       (ck:loc), RET #ck; own_MemKVClerk ck γ.(coord_kv_gn)
  }}}
.
Proof.
  iIntros (Φ) "#Hcoord HΦ".
  rewrite /MakeMemKVClerk.
  wp_lam.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.  Opaque slice.T. }
  iIntros (cck) "Hcck".
  wp_pures.
  wp_apply (wp_allocStruct).
  { Transparent slice.T. repeat econstructor.  Opaque slice.T. }
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  iDestruct (struct_fields_split with "Hcck") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_apply (wp_MakeRPCClient).
  iIntros (cl) "Hcl".
  wp_loadField.
  wp_storeField.
  wp_bind (MakeShardClerkSet #()).
  rewrite /MakeShardClerkSet.
  wp_lam.
  replace (ref (InjLV #null))%E with (NewMap (struct.ptrT MemKVShardClerk)) by auto.
  wp_apply (wp_NewMap).
  iIntros (mref_set) "Hmap_set".
  wp_apply (wp_allocStruct).
  { eauto. }
  iIntros (clset) "Hset".
  wp_storeField.
  wp_loadField.
  wp_apply (wp_MemKVCoordClerk__GetShardMap with "[cl Hcl]").
  { rewrite /own_MemKVCoordClerk. iExists _, _, _. iFrame "cl".
    iSplit; last first.
    { iSplit.
      { iExact "Hcoord". }
      { iExact "Hcl". }
    }
    eauto.
  }
  iIntros (shardMap_sl shardMapping) "(Hcck & HshardMap_sl & %Hlen & #Hall_are_shard_servers)".
  Transparent slice.T.
  wp_storeField.
  Opaque slice.T.
  iModIntro. iApply "HΦ".
  iExists _, _, _, _. iFrame.
  iFrame "% #". iExists _, _.
  iFrame "Hmap_set". rewrite big_sepM_empty; iSplit; last done.
  iDestruct (struct_fields_split with "Hset") as "HH".
  iNamed "HH". eauto.
Qed.

Lemma KVClerk__Get (ck:loc) (γ:gname) (key:u64) :
⊢ {{{ own_MemKVClerk ck γ }}}
  <<< ∀∀ v, kvptsto γ key v >>>
    MemKVClerk__Get #ck #key @ ∅
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

  assert (int.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (int.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".

  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet]").
  { iFrame "HH". }
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_MemKVShardClerk__Get with "[Hatomic $HshardCk $Hrep]").
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
    iDestruct "Hpost" as "(Hrep & Hval_sl & HΦ)".
    wp_load.
    iMod (readonly_load with "Hval_sl") as (?) "Hval_sl".
    iModIntro.
    iApply "HΦ".
    iFrame.
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iExists _, _, _, _. by iFrame "#∗".
  }
  {
    wp_loadField.
    iDestruct "HshardGetPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_MemKVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_apply (wp_storeField with "HshardMap").
    { apply slice_val_ty. }
    iIntros "HshardMap".
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "[_ $]".
    iExists _,_,_,_; by iFrame "#∗".
  }
Qed.

(* Sequential spec *)
Lemma KVClerk__Get_seq (ck:loc) (γ:gname) (key:u64) (v:list u8) :
  {{{ own_MemKVClerk ck γ ∗ kvptsto γ key v }}}
    MemKVClerk__Get #ck #key @ ⊤
  {{{ val_sl q, RET slice_val val_sl;
      own_MemKVClerk ck γ ∗ kvptsto γ key v ∗ typed_slice.is_slice_small val_sl byteT q%Qp v
  }}}.
Proof using Type*.
  iIntros (Φ) "(Hclerk & Hkey) HΦ".
  iApply (KVClerk__Get with "Hclerk").
  iApply fupd_mask_intro; first done. iNext.
  iIntros "Hclose". iExists _. iFrame "Hkey".
  iIntros "Hkey". iMod "Hclose" as "_". iModIntro.
  iIntros (??) "[Hclerk Hsl]". iApply "HΦ". iFrame.
Qed.

Lemma KVClerk__MGet (ck:loc) (γ:gname) (keys_sl:Slice.t) (keys_vals:list (u64 * list u8)) q :
  {{{ □ own_MemKVClerk ck γ (* FIXME this cannot be satisfied *) ∗
      typed_slice.is_slice_small keys_sl uint64T q (keys_vals.*1) ∗
      [∗ list] key_val ∈ keys_vals, kvptsto γ key_val.1 key_val.2
  }}}
    MemKVClerk__MGet #ck (slice_val keys_sl) @ ⊤
  {{{ (vals_sl:Slice.t) (val_sls:list Slice.t), RET slice_val vals_sl;
      own_MemKVClerk ck γ ∗
      typed_slice.is_slice_small keys_sl uint64T q (keys_vals.*1) ∗
      typed_slice.is_slice_small vals_sl (slice.T byteT) 1 val_sls ∗
      [∗ list] key_val;sl ∈ keys_vals;val_sls, kvptsto γ key_val.1 key_val.2 ∗
        readonly (typed_slice.is_slice_small sl byteT 1 key_val.2)
  }}}.
Proof using Type*.
  iIntros (Φ) "(#Hclerk & Hkeys_sl & Hkeys) HΦ". wp_lam.
  wp_apply wp_slice_len.
  wp_apply (typed_slice.wp_NewSlice (V:=Slice.t)).
  iIntros (vals_sl) "Hvals_sl".
  wp_apply wp_slice_len.

  wp_apply (wp_Multipar
    (λ i, ∃ (key:u64) val, ⌜keys_vals !! i = Some (key, val)⌝ ∗
      (keys_sl.(Slice.ptr) +ₗ[uint64T] i) ↦[uint64T] #key ∗
      kvptsto γ key val ∗
      (vals_sl.(Slice.ptr) +ₗ[slice.T byteT] i) ↦[slice.T byteT] slice_val Slice.nil)%I
    (λ i, ∃ (key:u64) val (val_sl:Slice.t), ⌜keys_vals !! i = Some (key, val)⌝ ∗
      (keys_sl.(Slice.ptr) +ₗ[uint64T] i) ↦[uint64T] #key ∗
      kvptsto γ key val ∗
      (vals_sl.(Slice.ptr) +ₗ[slice.T byteT] i) ↦[slice.T byteT] slice_val val_sl ∗
      readonly (typed_slice.is_slice_small val_sl byteT 1 val))%I
    keys_sl.(Slice.sz)
    with "[] [Hkeys_sl Hkeys Hvals_sl]").
  {
    iIntros "!> %i %Hi Hpre".
    iDestruct "Hpre" as (key val) "(%Hkv & Hkey_l & Hkey & Hval_l)".
    wp_pures.

    (* Breaking the SLiceGet (and later SliceSet) abstraction -- we only
       own that one element, not the entire slice! *)
    rewrite /SliceGet. wp_pures.
    wp_apply wp_slice_ptr. wp_pures.
    replace (int.nat i : Z) with (int.Z i) by word.
    wp_load.

    wp_apply (KVClerk__Get_seq with "[$Hkey //]").
    iIntros (val_sl qval_sl) "(_ & Hkey & Hval_sl)".

    rewrite /SliceSet. wp_pures.
    wp_apply wp_slice_ptr. wp_pures.
    wp_store.

    iExists _, _, _.
    iMod (readonly_alloc with "[Hval_sl]") as "$"; first done.
    eauto with iFrame. }
Abort.

Lemma KVClerk__Put (ck:loc) (γ:gname) (key:u64) (val_sl:Slice.t) (v:list u8):
⊢ {{{ own_MemKVClerk ck γ ∗ readonly (typed_slice.is_slice_small val_sl byteT 1 v) }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    MemKVClerk__Put #ck #key (slice_val val_sl) @ ∅
  <<< kvptsto γ key v >>>
  {{{ RET #(); own_MemKVClerk ck γ }}}.
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
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  assert (int.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (int.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet $HH]").
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_MemKVShardClerk__Put with "[Hatomic $Hval_sl $HshardCk]").
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
    iModIntro. iExists _, _, _, _. by iFrame "#∗".
  }
  {
    wp_loadField.
    iDestruct "HshardPutPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_MemKVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_apply (wp_storeField with "HshardMap").
    { apply slice_val_ty. }
    iIntros "HshardMap".
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "[_ $]".
    iFrame.
    iExists _,_,_,_. by iFrame "#∗".
  }
Qed.

Lemma KVClerk__ConditionalPut (ck:loc) (γ:gname) (key:u64) (expv_sl newv_sl:Slice.t) (expv newv:list u8):
⊢ {{{ own_MemKVClerk ck γ ∗
      readonly (typed_slice.is_slice_small expv_sl byteT 1 expv) ∗
      readonly (typed_slice.is_slice_small newv_sl byteT 1 newv) }}}
  <<< ∀∀ oldv, kvptsto γ key oldv >>>
    MemKVClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) @ ∅
  <<< kvptsto γ key (if bool_decide (expv = oldv) then newv else oldv) >>>
  {{{ RET #(bool_decide (expv = oldv));
      own_MemKVClerk ck γ }}}.
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
  iDestruct (typed_slice.is_slice_small_acc with "HshardMap_sl") as "[Hsmall_sl HslClose]".

  assert (int.nat sid < length shardMapping)%nat as HsidLe_nat by word.
  eapply list_lookup_lt in HsidLe_nat.
  destruct HsidLe_nat as [hostID HsidLe_nat].
  wp_apply (typed_slice.wp_SliceGet (V:=u64) with "[$Hsmall_sl]").
  {
    iPureIntro.
    done.
  }
  iIntros "Hsmall_sl".
  wp_pures.
  wp_loadField.

  unfold all_are_shard_servers.
  iDestruct ("HshardServers" $! (int.nat sid) hostID HsidLe_nat) as "HH".
  iNamed "HH".
  wp_apply (wp_ShardClerkSet__GetClerk with "[$HshardClerksSet $HH]").
  iClear "HH".

  iIntros (?) "(HshardCk & HcloseShardSet)".

  wp_pures.
  rewrite difference_empty_L.
  wp_apply (wp_MemKVShardClerk__ConditionalPut _ _ _ _ _ _ _ _ (λ b, own_MemKVClerk ck γ -∗ Φ #b)%I
    with "[Hatomic $HshardCk Hsucc]").
  {
    iFrame "#".
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
    iDestruct "HshardCondPutPost" as "(HshardCk & [[%Hbad _]|[_ Hpost]])".
    { by exfalso. }
    iDestruct "Hpost" as (succ) "(Hsucc & HΦ)".
    wp_load.
    iApply "HΦ". iModIntro.
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    iDestruct ("HslClose" with "Hsmall_sl") as "?".
    iFrame. iExists _, _, _, _. by iFrame "#∗".
  }
  {
    wp_loadField.
    iDestruct "HshardCondPutPost" as "(HshardCk & [Hatomic|[%Hbad _]])"; last first.
    { exfalso. naive_solver. }
    iDestruct ("HcloseShardSet" with "HshardCk") as "HshardSet".
    wp_apply (wp_MemKVCoordClerk__GetShardMap with "[$HcoordCk_own]").
    iIntros (shardMap_sl' shardMapping') "(HcoordCk_own & HshardMap_sl & %Hlength & #HshardServers')".
    wp_apply (wp_storeField with "HshardMap").
    { apply slice_val_ty. }
    iIntros "HshardMap".
    wp_pures.
    iLeft.
    iModIntro.

    iSplitL ""; first done.
    iDestruct "Hatomic" as "(_ & $ & Hsucc)".
    iFrame.
    iExists _,_,_,_; by iFrame "#∗".
  }
Qed.

End memkv_clerk_proof.
