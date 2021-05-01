From Perennial.program_proof Require Import dist_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

Section memkv_shard_clerk_proof.
Context `{!heapG Σ (ext:=grove_op) (ffi:=grove_model), rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_MakeFreshKVClerk (host:u64) γ :
  is_shard_server host γ -∗
  {{{
       True
  }}}
    MakeFreshKVClerk #host
  {{{
       (ck:loc), RET #ck; own_MemKVShardClerk ck γ
  }}}
.
Proof.
  iIntros "#His_shard !#" (Φ) "_ HΦ".
  wp_lam.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (ck) "Hck".
  iDestruct (struct_fields_split with "Hck") as "HH".
  iNamed "HH".
  wp_pures.
  wp_apply (wp_MakeRPCClient).
  iIntros (cl) "Hcl".
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
  wp_forBreak_cond.

  wp_pures.

  wp_apply (typed_slice.wp_NewSlice (V:=u8)).
  iIntros (req_sl) "Hreq_sl".
  wp_loadField.
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iNamed "HrawRep".
  wp_apply (wp_RPCClient__Call with "[$HfreshSpec $Hcl $Hreq_sl $HrawRep]").
  { done. }
  iIntros (???) "(HrawRep & Hcl & Hreq_sl & Hrep_sl & Hpost)".
  wp_pures.
  wp_if_destruct.
  { (* continue *)
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iExists _; iFrame.
  }
  (* got reply *)
  iRight.
  iDestruct "Hpost" as "[%Hbad|[_ Hpost]]"; first naive_solver.
  iModIntro. iSplitL ""; first done.
  wp_pures.
  wp_load.
  iDestruct "Hpost" as (??) "Hcid".
  wp_apply (wp_decodeUint64 with "[$Hrep_sl]").
  { done. }
  wp_storeField.
  wp_storeField.
  iApply "HΦ".
  iModIntro.
  iExists _, _, _, _.
  rewrite is_shard_server_unfold.
  iFrame "seq cid cl". iFrame "Hcid Hcl".
  iSplit.
  { iFrame "#". }
  iFrame "#".
  iFrame "∗#".
  iPureIntro.
  word.
  Unshelve. exact: tt.
Qed.

Definition own_shard_phys kvs_ptr sid (kvs:gmap u64 (list u8)) : iProp Σ :=
  ∃ (mv:gmap u64 val),
  map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
  ([∗ set] k ∈ (fin_to_set u64),
           ⌜shardOfC k ≠ sid⌝ ∨ (∃ vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice vsl byteT (1%Qp) (default [] (kvs !! k))) )
.

Lemma wp_MemKVShardClerk__InstallShard γ (ck:loc) (sid:u64) (kvs_ref:loc) (kvs:gmap u64 (list u8)) :
  {{{
       own_MemKVShardClerk ck γ ∗
       own_shard_phys kvs_ref sid kvs ∗
       own_shard γ.(kv_gn) sid kvs ∗
       ⌜int.Z sid < uNSHARD⌝
  }}}
    MemKVShardClerk__InstallShard #ck #sid #kvs_ref
  {{{
       RET #();
       own_MemKVShardClerk ck γ
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hphys & Hghost & %HsidLe)".
  iNamed "Hclerk".
  wp_lam.
  wp_pures.

  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (l) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".

  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_storeField.
  wp_storeField.

  wp_loadField.
  wp_loadField.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).

  wp_loadField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  iAssert (∃ rep_sl, rawRep ↦[slice.T byteT] (slice_val rep_sl) )%I with "[HrawRep]" as "HrawRep".
  {
    rewrite (zero_slice_val).
    iExists _; iFrame.
  }
  iAssert (own_InstallShardRequest l _) with "[CID Seq Sid Kvs Hphys]" as "Hargs".
  {
    iDestruct "Hphys" as (?) "[H HH]".
    iExists _, _.
    instantiate (1:=(mkInstallShardC _ _ _ _)).
    iFrame.
    iSimpl.
    iPureIntro; word.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |}  (own_shard γ.(kv_gn) sid kvs) (λ _, True)%I with "His_rpc Hcrpc [Hghost]") as "[Hcrpc HreqInv]".
  { done. }
  { simpl. word. }
  { iNext. iFrame. }
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeInstallShardRequest with "[$Hargs]").
  iIntros (??) "(%Henc & Hsl & Hargs)".
  wp_loadField.
  wp_apply (wp_RPCClient__Call with "[$HinstallSpec $Hsl $HrawRep $Hcl_own]").
  {
    iModIntro.
    iNext.
    iExists (mkInstallShardC _ _ _ _); iFrame.
    iFrame "HreqInv".
    iPureIntro.
    split.
    {
      done.
    }
    simpl.
    done.
  }
  iIntros (???) "(Hrep & Hcl_own & Hreq_sl & Hrep_sl)".
  wp_pures.
  wp_if_destruct.
  {
    wp_pures.
    iLeft.
    iModIntro.
    iSplitL ""; first done.
    iFrame.
    iExists _; iFrame.
  }
  (* got a reply *)
  iRight.
  iSplitL ""; first done.
  iApply "HΦ".
  iExists _, _, _, _.
  rewrite is_shard_server_unfold.
  iModIntro.
  iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
  iSplit.
  { iFrame "#". }
  iPureIntro.
  simpl. word.
Qed.

Lemma wp_MemKVShardClerk__Put Eo Ei γ (ck:loc) (key:u64) (v:list u8) value_sl Q :
  {{{
       (|NC={Eo,Ei}=> (∃ oldv, kvptsto γ.(kv_gn) key oldv ∗ (kvptsto γ.(kv_gn) key v -∗ |NC={Ei,Eo}=> Q))) ∗
       typed_slice.is_slice value_sl byteT 1%Qp v ∗
       own_MemKVShardClerk ck γ
  }}}
    MemKVShardClerk__Put #ck #key (slice_val value_sl)
  {{{
       (e:u64), RET #e;
       typed_slice.is_slice value_sl byteT 1%Qp v ∗
       own_MemKVShardClerk ck γ ∗ (
       ⌜e ≠ 0⌝ ∗
        (|NC={Eo,Ei}=> (∃ oldv, kvptsto γ.(kv_gn) key oldv ∗ (kvptsto γ.(kv_gn) key v -∗ |NC={Ei,Eo}=> Q)))
        ∨
        ⌜e = 0⌝ ∗ Q
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hval_sl & Hck)".
  iNamed "Hck".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { rewrite zero_slice_val. naive_solver. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_storeField.
  wp_apply (wp_storeField with "Value").
  { apply slice_val_ty. }
  iIntros "Value".

  wp_loadField.
  wp_loadField.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).

  wp_loadField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  iAssert (∃ rep_sl, rawRep ↦[slice.T byteT] (slice_val rep_sl) )%I with "[HrawRep]" as "HrawRep".
  {
    rewrite (zero_slice_val).
    iExists _; iFrame.
  }
  iAssert (own_PutRequest args_ptr value_sl {| PR_CID := cid; PR_Seq := seq; PR_Key := key; PR_Value := v |}) with "[CID Seq Key Value Hval_sl]" as "Hargs".
  {
    iFrame. simpl. iPureIntro; word.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardPut Eo Ei γ key Q v) (PostShardPut Eo Ei γ key Q v) with "His_rpc Hcrpc [Hkvptsto]") as "[Hcrpc HreqInv]".
  { done. }
  { simpl. word. }
  { iNext. iFrame. }
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodePutRequest _ _ (mkPutRequestC _ _ _ _) with "[$Hargs]").
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call with "[$HputSpec $Hreq_sl $HrawRep $Hcl_own]").
  {
    iModIntro.
    iModIntro.
    iExists (mkPutRequestC _ _ _ _).
    iSplitL ""; first done.
    instantiate (3:= (Eo,Ei,Q,γreq)).
    simpl.
    iFrame "HreqInv".
  }
  iIntros (b rep_sl' repData) "HcallPost".
  wp_if_destruct.
  {
    wp_pures.
    iModIntro.
    iLeft.
    iFrame.
    iDestruct "HcallPost" as "(HrawRep & $ & HcallPost)".
    iSplitL ""; first done.
    iExists _; iFrame "HrawRep".
  }
  {
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HcallPost" as "(HrawRep & Hcl_own & Hreq_sl & Hrep_sl & [%Hbad | HcallPost ])".
    { exfalso. naive_solver. }
    iDestruct "HcallPost" as "(_ & >Hpost)".
    wp_load.
    iDestruct "Hpost" as (??) "(% & % & Hreceipt)".
    wp_apply (wp_decodePutReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".
    replace (req) with ({| PR_CID := cid; PR_Seq := seq; PR_Key := key ; PR_Value := v|}); last first.
    { eapply has_encoding_PutRequest_inj; done. }

    iDestruct "Hreceipt" as "[Hbad|Hreceipt]".
    {
      iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
      exfalso.
      move: Hbad.
      simpl.
      word.
    }
    iDestruct "Hreceipt" as (? ?) "Hreceipt".
    iMod (get_request_post with "HreqInv Hreceipt Htok") as "Hpost".
    { done. }
    (* Doing get_request_post here so we can strip off a ▷ *)

    iNamed "Hrep".
    wp_pures.
    wp_loadField.
    iApply "HΦ".
    iSplitL "Hreq".
    {
      iNamed "Hreq"; iFrame.
    }
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _.
      rewrite is_shard_server_unfold.
      iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
      iSplit.
      { iFrame "#". }
      iPureIntro. word.
    }
    iDestruct "Hpost" as "[Hpost|Hpost]".
    {
      iLeft. iDestruct "Hpost" as "[$ $]".
    }
    {
      iRight.
      iDestruct "Hpost" as "($&HQ)".
      iFrame.
    }
  }
Qed.

Lemma wp_MemKVShardClerk__Get Eo Ei γ (ck:loc) (key:u64) (value_ptr:loc) Q :
  {{{
       (|NC={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v -∗ |NC={Ei,Eo}=> Q v))) ∗
       own_MemKVShardClerk ck γ ∗
       (∃ dummy_sl, value_ptr ↦[slice.T byteT] (slice_val dummy_sl))
  }}}
    MemKVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e;
       own_MemKVShardClerk ck γ ∗ (
       ⌜e ≠ 0⌝ ∗
        (|NC={Eo,Ei}=> (∃ v, kvptsto γ.(kv_gn) key v ∗ (kvptsto γ.(kv_gn) key v -∗ |NC={Ei,Eo}=> Q v))) ∗
        (∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl)) ∨

        ⌜e = 0⌝ ∗
              ∃ some_sl v q, value_ptr ↦[slice.T byteT] (slice_val some_sl) ∗
                                     typed_slice.is_slice_small some_sl byteT q%Qp v ∗
                                     Q v
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hck & Hval)".
  iNamed "Hck".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_loadField.
  wp_storeField.

  wp_loadField.
  wp_storeField.
  wp_storeField.

  wp_loadField.
  wp_loadField.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).

  wp_loadField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  iAssert (∃ rep_sl, rawRep ↦[slice.T byteT] (slice_val rep_sl) )%I with "[HrawRep]" as "HrawRep".
  {
    rewrite (zero_slice_val).
    iExists _; iFrame.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardGet Eo Ei γ key Q) (PostShardGet Eo Ei γ key Q) with "His_rpc Hcrpc [Hkvptsto]") as "[Hcrpc HreqInv]".
  { done. }
  { simpl. word. }
  { iNext. iFrame. }
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeGetRequest _ (mkGetRequestC _ _ _) with "[CID Seq Key]").
  {
    rewrite /own_GetRequest /=.
    iFrame.
    iPureIntro.
    simpl.
    word.
  }
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call with "[$HgetSpec $Hreq_sl $HrawRep $Hcl_own]").
  {
    iModIntro.
    iModIntro.
    iExists (mkGetRequestC _ _ _).
    iSplitL ""; first done.
    instantiate (2:= (Eo,Ei,Q,γreq)).
    simpl.
    iFrame "HreqInv".
  }
  iIntros (b rep_sl' repData) "HcallPost".
  wp_if_destruct.
  {
    wp_pures.
    iModIntro.
    iLeft.
    iFrame.
    iDestruct "HcallPost" as "(HrawRep & $ & HcallPost)".
    iSplitL ""; first done.
    iNamed "Hreq".
    iFrame.
    iExists _; iFrame "HrawRep".
  }
  {
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HcallPost" as "(HrawRep & Hcl_own & Hreq_sl & Hrep_sl & [%Hbad | HcallPost ])".
    { exfalso. naive_solver. }
    iDestruct "HcallPost" as "(_ & >Hpost)".
    wp_load.
    iDestruct "Hpost" as (??) "(% & % & Hreceipt)".
    wp_apply (wp_decodeGetReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".
    replace (req) with ({| GR_CID := cid; GR_Seq := seq; GR_Key := key |}); last first.
    { eapply has_encoding_GetRequest_inj; done. }

    iDestruct "Hreceipt" as "[Hbad|[% Hreceipt]]".
    {
      iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
      exfalso.
      move: Hbad.
      simpl.
      word.
    }
    iMod (get_request_post with "HreqInv Hreceipt Htok") as "Hpost".
    { done. }
    (* Doing get_request_post here so we can strip off a ▷ *)

    iNamed "Hrep".
    wp_pures.
    wp_loadField.
    iNamed "Hval".
    wp_store.
    wp_loadField.
    iApply "HΦ".
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _.
      iFrame.
      rewrite is_shard_server_unfold.
      iSplit.
      { iFrame "#". }
      iPureIntro. word.
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
  }
Qed.

Lemma wp_MemKVShardClerk__ConditionalPut Eo Ei γ (ck:loc) (key:u64) (expv newv:list u8) expv_sl newv_sl (succ_ptr:loc) Q :
  {{{
       (|NC={Eo,Ei}=> (∃ oldv, kvptsto γ.(kv_gn) key oldv ∗
         (let succ := bool_decide (expv = oldv) in kvptsto γ.(kv_gn) key (if succ then newv else oldv) -∗ |NC={Ei,Eo}=> Q succ))) ∗
       typed_slice.is_slice expv_sl byteT 1%Qp expv ∗
       typed_slice.is_slice newv_sl byteT 1%Qp newv ∗
       own_MemKVShardClerk ck γ ∗
       (∃ b : bool, succ_ptr ↦[boolT] #b)
  }}}
    MemKVShardClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) #succ_ptr
  {{{
       (e:u64), RET #e;
       typed_slice.is_slice expv_sl byteT 1%Qp expv ∗
       typed_slice.is_slice newv_sl byteT 1%Qp newv ∗
       own_MemKVShardClerk ck γ ∗ (
       ⌜e ≠ 0⌝ ∗
        (|NC={Eo,Ei}=> (∃ oldv, kvptsto γ.(kv_gn) key oldv ∗
         (let succ := bool_decide (expv = oldv) in kvptsto γ.(kv_gn) key (if succ then newv else oldv) -∗ |NC={Ei,Eo}=> Q succ))) ∗
       (∃ b : bool, succ_ptr ↦[boolT] #b)
        ∨
        ⌜e = 0⌝ ∗ ∃ succ : bool, succ_ptr ↦[boolT] #succ ∗ Q succ
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hexpv_sl & Hnewv_sl & Hck & Hsucc)".
  iNamed "Hck".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { rewrite zero_slice_val. naive_solver. }
  iIntros (args_ptr) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "HH".
  iNamed "HH".
  wp_pures.
  wp_loadField.
  wp_storeField.
  wp_loadField.
  wp_storeField.
  wp_storeField.
  wp_apply (wp_storeField with "ExpectedValue").
  { apply slice_val_ty. }
  iIntros "ExpValue".
  wp_apply (wp_storeField with "NewValue").
  { apply slice_val_ty. }
  iIntros "NewValue".

  wp_loadField.
  wp_loadField.
  wp_apply wp_Assume.
  rewrite bool_decide_eq_true.
  iIntros (Hoverflow).

  wp_loadField.
  wp_storeField.

  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rawRep) "HrawRep".
  wp_pures.

  iAssert (∃ rep_sl, rawRep ↦[slice.T byteT] (slice_val rep_sl) )%I with "[HrawRep]" as "HrawRep".
  {
    rewrite (zero_slice_val).
    iExists _; iFrame.
  }
  iAssert (own_ConditionalPutRequest args_ptr expv_sl newv_sl {| CPR_CID := cid; CPR_Seq := seq; CPR_Key := key; CPR_ExpValue := expv; CPR_NewValue := newv |}) with "[CID Seq Key ExpValue NewValue Hexpv_sl Hnewv_sl]" as "Hargs".
  {
    iFrame. simpl. iPureIntro; word.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iMod (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardConditionalPut Eo Ei γ key Q expv newv) (PostShardConditionalPut Eo Ei γ key Q expv newv) with "His_rpc Hcrpc [Hkvptsto]") as "[Hcrpc HreqInv]".
  { done. }
  { simpl. word. }
  { iNext. iFrame. }
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeConditionalPutRequest _ _ _ (mkConditionalPutRequestC _ _ _ _ _) with "[$Hargs]").
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call with "[$HconditionalPutSpec $Hreq_sl $HrawRep $Hcl_own]").
  {
    iModIntro.
    iModIntro.
    iExists (mkConditionalPutRequestC _ _ _ _ _).
    iSplitL ""; first done.
    instantiate (3:= (Eo,Ei,Q,γreq)).
    simpl.
    iFrame "HreqInv".
  }
  iIntros (b rep_sl' repData) "HcallPost".
  wp_if_destruct.
  {
    wp_pures.
    iModIntro.
    iLeft.
    iFrame.
    iDestruct "HcallPost" as "(HrawRep & $ & HcallPost)".
    iSplitL ""; first done.
    iExists _; iFrame "HrawRep".
  }
  {
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    iDestruct "HcallPost" as "(HrawRep & Hcl_own & Hreq_sl & Hrep_sl & [%Hbad | HcallPost ])".
    { exfalso. naive_solver. }
    iDestruct "HcallPost" as "(_ & >Hpost)".
    wp_load.
    iDestruct "Hpost" as (??) "(% & % & Hreceipt)".
    wp_apply (wp_decodeConditionalPutReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".
    replace (req) with ({| CPR_CID := cid; CPR_Seq := seq; CPR_Key := key ; CPR_ExpValue := expv; CPR_NewValue := newv |}); last first.
    { eapply has_encoding_ConditionalPutRequest_inj; done. }

    iDestruct "Hreceipt" as "[Hbad|Hreceipt]".
    {
      iDestruct (client_stale_seqno with "Hbad Hcrpc") as "%Hbad".
      exfalso.
      move: Hbad.
      simpl.
      word.
    }
    iDestruct "Hreceipt" as (?) "Hreceipt".
    iMod (get_request_post with "HreqInv Hreceipt Htok") as "Hpost".
    { done. }
    (* Doing get_request_post here so we can strip off a ▷ *)

    iNamed "Hrep".
    wp_pures.
    wp_loadField.
    iNamed "Hsucc".
    wp_store.
    wp_loadField.
    iApply "HΦ".
    rewrite assoc.
    iSplitL "Hreq".
    {
      iNamed "Hreq"; iFrame.
    }
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _.
      rewrite is_shard_server_unfold.
      iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
      iSplit.
      { iFrame "#". }
      iPureIntro. word.
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
  }
Qed.

End memkv_shard_clerk_proof.
