From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv Require Import memkv.
From Perennial.program_proof.lockservice Require Import rpc.
From Perennial.program_proof.memkv Require Export memkv_shard_definitions.

Section memkv_shard_clerk_proof.
Context `{!heapGS Σ (ext:=grove_op) (ffi:=grove_model), rpcG Σ ShardReplyC, rpcregG Σ, kvMapG Σ}.

Lemma wp_MakeFreshKVClerk (host:u64) γ :
  is_shard_server host γ -∗
  {{{
       True
  }}}
    MakeFreshKVClerk #host
  {{{
       (ck:loc), RET #ck; own_MemKVShardClerk ck γ.(kv_gn)
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
  wp_apply (wp_RPCClient__Call () with "[$Hcl $Hreq_sl $HrawRep]").
  { rewrite /has_handler. iFrame "HfreshSpec". done. }
  iIntros (?) "(Hcl & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iExists _; iFrame.
  }
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got reply *)
  iRight.
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
  iExists _, _, _, _, _.
  rewrite is_shard_server_unfold.
  iFrame "seq cid cl". iFrame "Hcid Hcl".
  iSplit.
  { iFrame "#". }
  iFrame "#".
  iFrame "∗#".
  iPureIntro.
  word.
Qed.

Definition own_shard_phys kvs_ptr sid (kvs:gmap u64 (list u8)) : iProp Σ :=
  ∃ (mv:gmap u64 val),
  map.is_map kvs_ptr 1 (mv, (slice_val Slice.nil)) ∗
  ([∗ set] k ∈ (fin_to_set u64),
           ⌜shardOfC k ≠ sid⌝ ∨ (∃ q vsl, ⌜default (slice_val Slice.nil) (mv !! k) = (slice_val vsl)⌝ ∗ typed_slice.is_slice_small vsl byteT q (default [] (kvs !! k))) )
.

Lemma wp_MemKVShardClerk__MoveShard γkv (ck : loc) (sid : u64) (dst : u64) γdst:
  {{{
       own_MemKVShardClerk ck γkv ∗
       is_shard_server dst γdst ∗
       ⌜int.Z sid < uNSHARD⌝ ∗
       ⌜γdst.(kv_gn) = γkv⌝
  }}}
    MemKVShardClerk__MoveShard #ck #sid #dst
  {{{ RET #();
        own_MemKVShardClerk ck γkv
  }}}.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & #Hserver & %Hid_lt & %Heq_kv_gn)".
  iNamed "Hclerk".
  wp_lam.
  wp_pures.
  wp_apply (wp_allocStruct).
  { naive_solver. }
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
  wp_forBreak_cond.
  wp_pures.

  wp_bind (encodeMoveShardRequest _).
  wp_apply (wp_encodeMoveShardRequest _ {| MR_Sid := sid; MR_Dst := dst |} with "[Sid Dst]").
  { iFrame. }
  iIntros (??) "(%Henc & Hsl & Hargs)".

  wp_loadField.
  iEval (rewrite is_shard_server_unfold) in "His_shard".
  iNamed "His_shard".
  iNamed "HrawRep".
  wp_apply (wp_RPCClient__Call _ with "[Hsl HrawRep Hcl_own]").
  { iFrame "HrawRep Hsl Hcl_own". iSplitL.
    { rewrite /has_handler. simpl. iFrame "HmoveSpec". }
    iModIntro. iNext. iExists _. iFrame "%". iSplit. 
    { iNext => /=. iFrame "Hserver". }
    { iPureIntro. congruence. }
  }
  iIntros (?) "(Hcl_own & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iNamed "Hargs". iFrame. iExists _. iFrame.
  }
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got reply *)
  iRight. iModIntro. iSplit; first done.
  iApply "HΦ". iExists _, _, _, _, _.
  iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
  iSplit; last eauto.
  iEval (rewrite is_shard_server_unfold).
  { iFrame "#". }
Qed.

Lemma wp_MemKVShardClerk__InstallShard γkv (ck:loc) (sid:u64) (kvs_ref:loc) (kvs:gmap u64 (list u8)) :
  {{{
       own_MemKVShardClerk ck γkv ∗
       own_shard_phys kvs_ref sid kvs ∗
       own_shard γkv sid kvs ∗
       ⌜int.Z sid < uNSHARD⌝
  }}}
    MemKVShardClerk__InstallShard #ck #sid #kvs_ref
  {{{
       RET #();
       own_MemKVShardClerk ck γkv
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
  iPoseProof (make_request {| Req_CID:=_; Req_Seq:= _ |}  (own_shard γ.(kv_gn) sid kvs) (λ _, True)%I with "His_rpc Hcrpc [Hghost]") as "Hmkreq".
  { done. }
  { simpl. word. }
  { iNext. rewrite Hγeq. iFrame. }
  iApply fupd_wp.
  iEval (rewrite global_groveG_inv_conv') in "Hmkreq".
  iApply (fupd_mask_weaken (↑replyTableInvN)); eauto.
  iIntros "Hclo". iMod "Hmkreq" as "[Hcrpc HreqInv]". iMod "Hclo". iModIntro.
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeInstallShardRequest with "[$Hargs]").
  iIntros (??) "(%Henc & Hsl & Hargs)".
  wp_loadField.
  wp_apply (wp_RPCClient__Call with "[$Hsl $HrawRep $Hcl_own]").
  {
    iEval (rewrite /has_handler) in "HinstallSpec". iFrame "HinstallSpec".
    iModIntro.
    iNext.
    iExists (mkInstallShardC _ _ _ _); iFrame.
    iEval (rewrite global_groveG_inv_conv').
    iFrame "HreqInv".
    iPureIntro.
    split.
    {
      done.
    }
    simpl.
    done.
  }
  iIntros (?) "(Hcl_own & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iExists _; iFrame.
  }
  iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
  (* got a reply *)
  iRight.
  iSplitL ""; first done.
  iApply "HΦ".
  iExists _, _, _, _, _.
  rewrite is_shard_server_unfold.
  iModIntro.
  iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
  iSplit.
  { iFrame "#". }
  iPureIntro.
  simpl. word.
Qed.

Lemma wp_MemKVShardClerk__Put γkv (ck:loc) (key:u64) (v:list u8) value_sl Q :
  {{{
       (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q))) ∗
       readonly (typed_slice.is_slice_small value_sl byteT 1%Qp v) ∗
       own_MemKVShardClerk ck γkv
  }}}
    MemKVShardClerk__Put #ck #key (slice_val value_sl)
  {{{
       (e:u64), RET #e;
       own_MemKVShardClerk ck γkv ∗ (
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
  iAssert (own_PutRequest args_ptr value_sl {| PR_CID := cid; PR_Seq := seq; PR_Key := key; PR_Value := v |}) with "[CID Seq Key Value]" as "Hargs".
  {
    iFrame "∗#". simpl. iPureIntro; word.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iPoseProof (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardPut γ.(kv_gn) key Q v) (PostShardPut γ.(kv_gn) key Q v) with "His_rpc Hcrpc [Hkvptsto]") as "Hmkreq".

  { done. }
  { simpl. word. }
  { iNext. rewrite Hγeq /PreShardPut. rewrite global_groveG_inv_conv'. iFrame. }
  iApply fupd_wp.
  iEval (rewrite global_groveG_inv_conv') in "Hmkreq".
  iApply (fupd_mask_weaken (↑replyTableInvN)); eauto.
  iIntros "Hclo". iMod "Hmkreq" as "[Hcrpc HreqInv]". iMod "Hclo". iModIntro.
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodePutRequest _ _ (mkPutRequestC _ _ _ _) with "[$Hargs]").
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call (Q, γreq, mkPutRequestC _ _ _ _) with "[$Hreq_sl $HrawRep $Hcl_own]").
  {
    iEval (rewrite /has_handler) in "HputSpec". iFrame "HputSpec".
    simpl.
    iModIntro.
    iModIntro.
    iSplitL ""; first done.
    simpl.
    rewrite -global_groveG_inv_conv'.
    iFrame "HreqInv".
  }
  iIntros (?) "(Hcl_own & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iExists _; iFrame.
  }
  {
    iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    wp_load.
    iDestruct "Hpost" as (?) "(% & Hreceipt)".
    wp_apply (wp_decodePutReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".

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
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _, _.
      rewrite is_shard_server_unfold.
      iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
      iFrame "#". iPureIntro.
      split; last done. word.
    }
    iDestruct "Hpost" as "[Hpost|Hpost]".
    {
      iLeft.
      iEval (rewrite -global_groveG_inv_conv').
      rewrite Hγeq.
      by iDestruct "Hpost" as "[$ $]".
    }
    {
      iRight.
      iDestruct "Hpost" as "($&HQ)".
      by iFrame.
    }
  }
Qed.

Lemma wp_MemKVShardClerk__Get γkv (ck:loc) (key:u64) (value_ptr:loc) Q :
  {{{
       (|={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v))) ∗
       own_MemKVShardClerk ck γkv ∗
       (∃ dummy_sl, value_ptr ↦[slice.T byteT] (slice_val dummy_sl))
  }}}
    MemKVShardClerk__Get #ck #key #value_ptr
  {{{
       (e:u64), RET #e;
       own_MemKVShardClerk ck γkv ∗ (
       ⌜e ≠ 0⌝ ∗
        (|={⊤,∅}=> (∃ v, kvptsto γkv key v ∗ (kvptsto γkv key v -∗ |={∅,⊤}=> Q v))) ∗
        (∃ some_sl, value_ptr ↦[slice.T byteT] (slice_val some_sl)) ∨

        ⌜e = 0⌝ ∗
              ∃ some_sl v, value_ptr ↦[slice.T byteT] (slice_val some_sl) ∗
                           readonly (typed_slice.is_slice_small some_sl byteT 1 v) ∗
                           Q v
        )
  }}}
.
Proof.
  iIntros (Φ) "Hpre HΦ".
  iDestruct "Hpre" as "(Hkvptsto & Hck & Hval)".
  iNamed "Hck".
  rewrite -Hγeq.
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
  iPoseProof (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardGet γ.(kv_gn) key Q) (PostShardGet γ.(kv_gn) key Q) with "His_rpc Hcrpc [Hkvptsto]") as "Hmkreq".
  { done. }
  { simpl. word. }
  { iNext. rewrite /PreShardGet. rewrite global_groveG_inv_conv'. iFrame. }
  iApply fupd_wp.
  iEval (rewrite global_groveG_inv_conv') in "Hmkreq".
  iApply (fupd_mask_weaken (↑replyTableInvN)); eauto.
  iIntros "Hclo". iMod "Hmkreq" as "[Hcrpc HreqInv]". iMod "Hclo". iModIntro.
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
  wp_apply (wp_RPCClient__Call (Q,γreq,mkGetRequestC _ _ _) with "[$Hreq_sl $HrawRep $Hcl_own]").
  {
    iEval (rewrite /has_handler) in "HgetSpec". iFrame "HgetSpec".
    iModIntro.
    iModIntro.
    iSplitL ""; first done.
    simpl.
    rewrite -global_groveG_inv_conv'.
    iFrame "HreqInv".
  }
  iIntros (?) "(Hcl_own & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iNamed "Hreq".
    iFrame.
    iExists _; by iFrame.
  }
  {
    iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    wp_load.
    iDestruct "Hpost" as (?) "(% & Hreceipt)".
    wp_apply (wp_decodeGetReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".

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
    { iExists _, _, _, _, _.
      iFrame.
      rewrite is_shard_server_unfold.
      iSplit.
      { iFrame "#". }
      iPureIntro. word.
    }
    iDestruct "Hpost" as "[Hpost|Hpost]".
    {
      iLeft. rewrite -global_groveG_inv_conv'. iDestruct "Hpost" as "[$ $]".
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

Lemma wp_MemKVShardClerk__ConditionalPut γkv (ck:loc) (key:u64) (expv newv:list u8) expv_sl newv_sl (succ_ptr:loc) Q :
  {{{
       (|={⊤,∅}=> (∃ oldv, kvptsto γkv key oldv ∗
         (let succ := bool_decide (expv = oldv) in kvptsto γkv key (if succ then newv else oldv) -∗ |={∅,⊤}=> Q succ))) ∗
       readonly (typed_slice.is_slice_small expv_sl byteT 1 expv) ∗
       readonly (typed_slice.is_slice_small newv_sl byteT 1 newv) ∗
       own_MemKVShardClerk ck γkv ∗
       (∃ b : bool, succ_ptr ↦[boolT] #b)
  }}}
    MemKVShardClerk__ConditionalPut #ck #key (slice_val expv_sl) (slice_val newv_sl) #succ_ptr
  {{{
       (e:u64), RET #e;
       own_MemKVShardClerk ck γkv ∗ (
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
  iNamed "Hck".
  rewrite -Hγeq.
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
    iFrame "∗#". simpl. iPureIntro; word.
  }
  rewrite is_shard_server_unfold.
  iNamed "His_shard".
  iPoseProof (make_request {| Req_CID:=_; Req_Seq:= _ |} (PreShardConditionalPut γ.(kv_gn) key Q expv newv) (PostShardConditionalPut γ.(kv_gn) key Q expv newv) with "His_rpc Hcrpc [Hkvptsto]") as "Hmkreq". 
  { done. }
  { simpl. word. }
  { iNext. rewrite /PreShardConditionalPut. rewrite global_groveG_inv_conv'. iFrame. }
  iApply fupd_wp.
  iEval (rewrite global_groveG_inv_conv') in "Hmkreq".
  iApply (fupd_mask_weaken (↑replyTableInvN)); eauto.
  iIntros "Hclo". iMod "Hmkreq" as "[Hcrpc HreqInv]". iMod "Hclo". iModIntro.
  iDestruct "HreqInv" as (?) "[#HreqInv Htok]".

  wp_forBreak_cond.
  iNamed "HrawRep".
  wp_pures.

  wp_apply (wp_encodeConditionalPutRequest _ _ _ (mkConditionalPutRequestC _ _ _ _ _) with "[$Hargs]").
  iIntros (reqData req_sl) "(%HencReq & Hreq_sl & Hreq)".
  wp_loadField.

  unfold is_shard_server.
  wp_apply (wp_RPCClient__Call (Q,γreq,mkConditionalPutRequestC _ _ _ _ _) with "[$Hreq_sl $HrawRep $Hcl_own]").
  {
    iEval (rewrite /has_handler) in "HconditionalPutSpec". iFrame "HconditionalPutSpec".
    iModIntro.
    iModIntro.
    iSplitL ""; first done.
    simpl.
    rewrite -global_groveG_inv_conv'.
    iFrame "HreqInv".
  }
  iIntros (?) "(Hcl_own & Hreq_sl & Hpost)".
  destruct err as [err|].
  { (* continue *)
    wp_pures. rewrite bool_decide_false; last by destruct err.
    wp_pures. iLeft.
    iFrame.
    iSplitL ""; first done.
    iModIntro. iExists _; iFrame.
  }
  {
    iDestruct "Hpost" as "(% & % & HrawRep & Hrep_sl & Hpost)"; wp_pures.
    iModIntro.
    iRight.
    iSplitL ""; first done.
    wp_pures.
    wp_load.
    iDestruct "Hpost" as (?) "(% & Hreceipt)".
    wp_apply (wp_decodeConditionalPutReply with "[$Hrep_sl]").
    { done. }
    iIntros (?) "Hrep".

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
    iSplitL "Hcl_own Hcrpc Hcl Hcid Hseq".
    { iExists _, _, _, _, _.
      rewrite is_shard_server_unfold.
      iFrame "Hcid Hseq Hcl Hcrpc Hcl_own".
      iSplit.
      { iFrame "#". }
      iPureIntro. word.
    }
    iDestruct "Hpost" as "[Hpost|Hpost]".
    {
      iLeft. rewrite -global_groveG_inv_conv'. iDestruct "Hpost" as "[$ $]".
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
