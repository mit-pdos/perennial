From Perennial.program_proof Require Import grove_prelude std_proof.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

#[local] Set Universe Polymorphism.

Section memkv_shard_clerk_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), erpcG Σ, urpcregG Σ, kvMapG Σ}.

Polymorphic Lemma wp_MakeFreshKVShardClerk (host:u64) (c:loc) γ :
  is_shard_server host γ -∗
  is_ConnMan c -∗
  {{{
       True
  }}}
    MakeFreshKVShardClerk #host #c
  {{{
       (ck:loc), RET #ck; own_KVShardClerk ck γ.(kv_gn)
  }}}
.
Proof.
  iIntros "#His_shard #Hc !#" (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_storeField.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.
  iAssert (∃ sl, rawRep ↦[slice.T byteT] (slice_val sl))%I with "[HrawRep]" as "HrawRep".
  {
    rewrite zero_slice_val.
    iExists _; iFrame.
  }

  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (req_sl) "Hreq_sl".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_loadField.
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iNamed "HrawRep".
  wp_apply (wp_ConnMan__CallAtLeastOnce (is_shard_server_freshSpec _) () with "[$Hreq_sl $HrawRep]").
  { simpl. iFrame "#". done. }
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got reply *)
  wp_load.
  iDestruct "Hpost" as (??) "Hcid".
  wp_apply (wp_DecodeUint64' with "[$Hrep_sl]").
  { done. }
  wp_apply (wp_erpc_MakeClient with "Hcid").
  iIntros (erpc) "Herpc".
  wp_storeField.
  iApply "HΦ".
  iModIntro.
  iExists _, _, _, _.
  rewrite is_shard_server_unfold.
  iFrame "erpc c host". iFrame "Herpc Hc".
  iSplit.
  { iFrame "#". }
  done.
Qed.

Definition own_shard_phys kvs_ptr sid (kvs:gmap u64 (list u8)) : iProp Σ :=
  ∃ (mv:gmap u64 val),
  "Hmap_phys" ∷ map.own_map kvs_ptr (DfracOwn 1) (mv, (slice_val Slice.nil)) ∗
  "%Hdom_phys" ∷ ⌜ dom kvs = dom mv ⌝ ∗
  ([∗ set] k ∈ (fin_to_set u64),
           (⌜shardOfC k ≠ sid ∧ mv !! k = None ∧ kvs !! k = None ⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.own_slice_small vsl byteT DfracDiscarded (default [] (kvs !! k)))))
.

(*
Definition own_shard_phys kvs_ptr sid (kvs:gmap u64 (list u8)) : iProp Σ :=
  ∃ (mv:gmap u64 val),
  "%Hdom_phys" ∷ ⌜ dom mv = dom kvs ⌝ ∗
  "Hmap_phys" ∷ map.own_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
  "%Hdom_sid" ∷ ⌜ (∀ k, shardOfC k = sid → k ∈ dom mv) ⌝ ∗
  ([∗ map] k ↦ vsl' ∈ mv, ∃ q vsl, ⌜ vsl' = (slice_val vsl)⌝ ∗ typed_slice.own_slice_small vsl byteT q (default [] (kvs !! k))).
*)

Lemma wp_KVShardClerk__MoveShard γkv (ck : loc) (sid : u64) (dst : u64) γdst:
  {{{
       own_KVShardClerk ck γkv ∗
       is_shard_server dst γdst ∗
       ⌜uint.Z sid < uNSHARD⌝ ∗
       ⌜ γdst.(kv_gn) = γkv ⌝
  }}}
    KVShardClerk__MoveShard #ck #sid #dst
  {{{ RET #();
        own_KVShardClerk ck γkv
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & #Hserver & %Hid_lt & %Heq_kv_gn)".
  subst.
  iNamed "Hclerk".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.
  iAssert (∃ sl, rawRep ↦[slice.T byteT] (slice_val sl))%I with "[HrawRep]" as "HrawRep".
  {
    rewrite zero_slice_val.
    iExists _; iFrame.
  }

  wp_pures.

  wp_bind (encodeMoveShardRequest _).
  wp_apply (wp_encodeMoveShardRequest _ {| MR_Sid := sid; MR_Dst := dst |} with "[Sid Dst]").
  { iFrame. }
  iIntros (??) "(%Henc & Hsl & Hargs)".

  wp_loadField.
  wp_loadField.
  iEval (rewrite is_shard_server_unfold) in "His_shard".
  iNamed "His_shard".
  iNamed "HrawRep".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_ConnMan__CallAtLeastOnce (is_shard_server_moveSpec_pre _ _) with "[$Hsl $HrawRep]").
  { iFrame "#". iExists _. iFrame "%". iFrame "Hserver". done. }
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got reply *)
  wp_pures. iModIntro. iApply "HΦ". iExists _, _, _, _.
  iFrame "Herpc erpc Hc Hhost Hc_own".
  iSplit; last eauto.
  iEval (rewrite is_shard_server_unfold).
  { iFrame "#". }
Qed.

Lemma wp_KVShardClerk__InstallShard γkv (ck:loc) (sid:u64) (kvs_ref:loc) (kvs:gmap u64 (list u8)) :
  {{{
       own_KVShardClerk ck γkv ∗
       own_shard_phys kvs_ref sid kvs ∗
       own_shard γkv sid kvs ∗
       ⌜uint.Z sid < uNSHARD⌝
  }}}
    KVShardClerk__InstallShard #ck #sid #kvs_ref
  {{{
       RET #();
       own_KVShardClerk ck γkv
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hphys & Hghost & %HsidLe)".
  iNamed "Hclerk". subst γkv.
  wp_lam.
  wp_pures.

  wp_apply (wp_allocStruct); first val_ty.
  iIntros (l) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".

  wp_storeField.
  wp_storeField.

  wp_apply (wp_encodeInstallShardRequest with "[Sid Kvs Hphys]").
  {
    iDestruct "Hphys" as (?) "[H HH]".
    instantiate (1:=(mkInstallShardC _ _)).
    iExists _, _.
    iFrame.
  }
  iIntros (??) "(%Henc & Hsl & Hargs)".
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  wp_loadField.
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_apply (wp_erpc_NewRequest (is_shard_server_installSpec _) () with "[$Herpc $Hsl Hghost]").
  { simpl.
    iExists (mkInstallShardC _ _); iFrame. simpl.
    iPureIntro.
    split.
    {
      done.
    }
    simpl.
    done.
  }
  clear req_sl. iIntros (y req req_sl) "(Hreq & #Hpre & Htakepost)".
  iDestruct (own_slice_to_small with "Hreq") as "Hreq".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_ConnMan__CallAtLeastOnce with "[$]").
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got a reply *)
  iMod ("Htakepost" with "Hpost") as "[Herpc Hpost]".
  iApply "HΦ". iModIntro.
  iExists _, _, _, _.
  rewrite is_shard_server_unfold.
  iFrame "Hc Hhost erpc Herpc Hc_own".
  iSplit.
  { iFrame "#". }
  done.
Qed.

Lemma wp_KVShardClerk__Put γkv (ck:loc) (key:u64) (v:list u8) value_sl Q :
  {{{
       (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q))) ∗
       typed_slice.own_slice_small value_sl byteT DfracDiscarded v ∗
       own_KVShardClerk ck γkv
  }}}
    KVShardClerk__Put #ck #key (slice_val value_sl)
  {{{
       (e:u64), RET #e;
       own_KVShardClerk ck γkv ∗ (
       ⌜e ≠ 0⌝ ∗
        (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q)))
        ∨
        ⌜e = 0⌝ ∗ Q
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & #Hval_sl & Hck)".
  iNamed "Hck". subst γkv.
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_storeField.

  wp_apply (wp_EncodePutRequest _ _ (mkPutRequestC _ _) with "[$Key $Value //]").
  iIntros (??) "(%Henc & Hsl & Hargs)".
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  wp_loadField.
  wp_apply (wp_erpc_NewRequest (is_shard_server_putSpec _) (_, _) with "[$Herpc $Hsl Hkvptsto]").
  { simpl. auto. }
  clear req_sl. iIntros (y req req_sl) "(Hreq & #Hpre & Htakepost)".
  iDestruct (own_slice_to_small with "Hreq") as "Hreq_sl".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  wp_loadField.
  wp_loadField.
  wp_apply (wp_ConnMan__CallAtLeastOnce with "[$]").
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  iMod ("Htakepost" with "Hpost") as "[Herpc Hpost]".
  wp_pures.
  wp_load.
  iDestruct "Hpost" as (?) "(% & Hpost)".
  wp_apply (wp_DecodePutReply with "[$Hrep_sl]").
  { done. }
  iIntros (?) "Hrep".

  wp_pures.
  wp_loadField.
  iApply "HΦ".
  iSplitL "Hc_own erpc Herpc Hc Hhost".
  { iExists _, _, _, _.
    rewrite is_shard_server_unfold.
    iFrame "Hc Hhost erpc Herpc Hc_own".
    iFrame "#". done.
  }
  iDestruct "Hpost" as "[Hpost|Hpost]".
  {
    iLeft.
      by iDestruct "Hpost" as "[$ $]".
  }
  {
    iRight.
    iDestruct "Hpost" as "($&HQ)".
      by iFrame.
  }
Qed.

Lemma wp_KVShardClerk__Get γkv (ck:loc) (key:u64) (value_ptr:loc) Q :
  {{{
       (|={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v))) ∗
       own_KVShardClerk ck γkv ∗
       (∃ dummy_sl, value_ptr ↦[slice.T byteT] (slice_val dummy_sl))
  }}}
    KVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e;
       own_KVShardClerk ck γkv ∗ (
       ⌜e ≠ 0⌝ ∗
        (|={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v))) ∗
        (∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl)) ∨

        ⌜e = 0⌝ ∗
              ∃ some_sl v, value_ptr ↦[slice.T byteT] (slice_val some_sl) ∗
                           typed_slice.own_slice_small some_sl byteT DfracDiscarded v ∗
                           Q v
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hck & Hval)".
  iNamed "Hck". subst γkv.
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_storeField.

  wp_apply (wp_EncodeGetRequest _ (mkGetRequestC _) with "Key").
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_loadField.
  wp_apply (wp_erpc_NewRequest (is_shard_server_getSpec _) (_, _) with "[$Herpc $Hreq_sl Hkvptsto]").
  { simpl. auto. }
  clear req_sl. iIntros (y req req_sl) "(Hreq_sl & #Hpre & Htakepost)".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  wp_loadField.
  wp_loadField.
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  wp_apply (wp_ConnMan__CallAtLeastOnce with "[$]").
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  iMod ("Htakepost" with "Hpost") as "[Herpc Hpost]".
  wp_load.
  iDestruct "Hpost" as (?) "(% & Hpost)".
  wp_apply (wp_DecodeGetReply with "[$Hrep_sl]").
  { done. }
  iIntros (?) "Hrep".
  iNamed "Hrep".

  wp_pures.
  iNamed "Hval".
  wp_loadField.
  wp_store.
  wp_loadField.
  iApply "HΦ".
  iSplitL "Hc_own erpc Herpc Hc Hhost".
  { iExists _, _, _, _.
    iFrame. iFrame "Hc_own".
    rewrite is_shard_server_unfold.
    iSplit.
    { iFrame "#". }
    done.
  }
  iDestruct "Hpost" as "[Hpost|Hpost]".
  {
    iLeft. iDestruct "Hpost" as "[$ $]".
    iExists _; iFrame.
  }
  {
    iRight.
    iDestruct "Hpost" as "($&HQ)".
    iExists _, _; iFrame.
    iFrame "HValue_sl".
  }
Qed.

Lemma wp_KVShardClerk__ConditionalPut γkv (ck:loc) (key:u64) (expv newv:list u8) expv_sl newv_sl (succ_ptr:loc) Q :
  {{{
       (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗
         (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗ |={∅,⊤}=> Q succ))) ∗
       typed_slice.own_slice_small expv_sl byteT DfracDiscarded expv ∗
       typed_slice.own_slice_small newv_sl byteT DfracDiscarded newv ∗
       own_KVShardClerk ck γkv ∗
       (∃ b : bool, succ_ptr ↦[boolT] #b)
  }}}
    KVShardClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) #succ_ptr
  {{{
       (e:u64), RET #e;
       own_KVShardClerk ck γkv ∗ (
       ⌜e ≠ 0⌝ ∗
        (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗
         (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗ |={∅,⊤}=> Q succ))) ∗
       (∃ b : bool, succ_ptr ↦[boolT] #b)
        ∨
        ⌜e = 0⌝ ∗ ∃ succ : bool, succ_ptr ↦[boolT] #succ ∗ Q succ
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & #Hexpv_sl & #Hnewv_sl & Hck & Hsucc)".
  iNamed "Hck". subst γkv.
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct); first val_ty.
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_storeField.
  wp_storeField.
  wp_storeField.

  wp_apply (wp_EncodeConditionalPutRequest _ _ _ (mkConditionalPutRequestC _ _ _) with "[Key ExpectedValue NewValue Hexpv_sl Hnewv_sl]").
  { iFrame. iFrame "#". }
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".
  wp_loadField.
  wp_apply (wp_erpc_NewRequest (is_shard_server_conditionalPutSpec _) (_, _) with "[$Herpc $Hreq_sl Hkvptsto]").
  { simpl. auto. }
  clear req_sl. iIntros (y req req_sl) "(Hreq_sl & #Hpre & Htakepost)".
  iDestruct (own_slice_to_small with "Hreq_sl") as "Hreq_sl".

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  wp_loadField.
  wp_loadField.
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  wp_apply (wp_ConnMan__CallAtLeastOnce with "[$]").
  iIntros "(Hreq_sl & Hpost)".
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  iMod ("Htakepost" with "Hpost") as "[Herpc Hpost]".
  wp_load.
  iDestruct "Hpost" as (?) "(% & Hpost)".
  wp_apply (wp_DecodeConditionalPutReply with "[$Hrep_sl]").
  { done. }
  iIntros (?) "Hrep".
  iNamed "Hrep".
  wp_pures.
  wp_loadField.
  iNamed "Hsucc".
  wp_store.
  wp_loadField.
  iApply "HΦ".
  iSplitL "Hc_own erpc Herpc Hc Hhost".
  { iExists _, _, _, _.
    rewrite is_shard_server_unfold.
    iFrame "Hc Hhost erpc Herpc Hc_own".
    iSplit.
    { iFrame "#". }
    done.
  }
  iDestruct "Hpost" as "[Hpost|Hpost]".
  {
    iLeft. iDestruct "Hpost" as "[$ $]".
    eauto with iFrame.
  }
  {
    iRight.
    iDestruct "Hpost" as "($&HQ)".
    eauto with iFrame.
  }
Qed.

End memkv_shard_clerk_proof.
