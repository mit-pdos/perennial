From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.ffi Require Import grove_ffi.
From Perennial.program_proof Require Import proof_prelude.
From Goose.github_com.mit_pdos.lockservice Require Import grove_common lockservice.
From Perennial.program_proof.lockservice Require Import common_proof.
From Perennial.program_proof.lockservice Require Export rpc.
From Goose.github_com.mit_pdos.lockservice Require Import grove_common.
From Perennial.goose_lang.lib.slice Require Import typed_slice.
From Perennial.program_proof Require Import marshal_proof.

Section rpc_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.
Context `{!rpcregG Σ}.

Record RPCValsC := mkRPCValsC
{
  U64_1:u64 ;
  U64_2:u64 ;
}.

#[refine] Global Instance RPCValC_into_val : into_val.IntoVal (RPCValsC) :=
  {
  to_val := λ x, (#x.(U64_1), (#x.(U64_2), #()))%V ;
  IntoVal_def := {| U64_1 := 0; U64_2 := 0 |} ;
  IntoVal_inj := _
  }.
Proof.
  intros x1 x2 [=].
  destruct x1. destruct x2.
  simpl in *. subst.
  done.
Defined.

Definition RPCRequest_own_ro (args_ptr:loc) (req : RPCRequestID) (args:RPCValsC) : iProp Σ :=
    "%" ∷ ⌜int.nat req.(Req_Seq) > 0⌝ ∗
    "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Args"] (into_val.to_val args)) ∗
    "#HArgsOwnCID" ∷ readonly (args_ptr ↦[RPCRequest.S :: "CID"] #req.(Req_CID)) ∗
    "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Seq"] #req.(Req_Seq))
.

Definition RPCReply_own (reply_ptr:loc) (r : @RPCReply (u64)) : iProp Σ :=
    "HReplyOwnStale" ∷ reply_ptr ↦[RPCReply.S :: "Stale"] #r.(Rep_Stale)
  ∗ "HReplyOwnRet" ∷ reply_ptr ↦[RPCReply.S :: "Ret"] (into_val.to_val r.(Rep_Ret))
.

Definition RPCServer_own_vol (sv:loc) (γrpc:rpc_names) (lastSeqM lastReplyM:gmap u64 u64) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc),
      "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr ∗
      "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr ∗
      "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM ∗
      "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM ∗
      "#Hlinv" ∷ is_RPCServer γrpc
.

Definition Reply64 := @RPCReply (u64).

Definition RPCClient_own_vol (cl_ptr:loc) (cid seqno:u64) (host:string) : iProp Σ :=
  ∃ (rawCl:loc),
    "%" ∷ ⌜int.nat seqno > 0⌝ ∗
    "Hcid" ∷ cl_ptr ↦[RPCClient.S :: "cid"] #cid ∗
    "Hseq" ∷ cl_ptr ↦[RPCClient.S :: "seq"] #seqno ∗
    "HrawCl" ∷ cl_ptr ↦[RPCClient.S :: "rawCl"] #rawCl ∗
    "HrawClOwn" ∷ grove_ffi.RPCClient_own rawCl host
.

Definition RPCClient_own (cl_ptr:loc) (host:string) γrpc : iProp Σ :=
  ∃ cid seqno,
    RPCClient_own_vol cl_ptr cid seqno host ∗
    RPCClient_own_ghost γrpc cid seqno
.

Lemma CheckReplyTable_spec (reply_ptr:loc) (req:RPCRequestID) (reply:Reply64) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
int.nat req.(Req_Seq) > 0 →
is_RPCServer γrpc -∗
{{{
    "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM ∗
    "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM ∗
    "Hreply" ∷ RPCReply_own reply_ptr reply
}}}
  CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(Req_CID) #req.(Req_Seq) #reply_ptr
{{{
     (b:bool) (reply':Reply64), RET #b; "Hreply" ∷ RPCReply_own reply_ptr reply' ∗
      "Hcases" ∷ ("%" ∷ ⌜b = false⌝ ∗
           "%" ∷ ⌜(int.Z req.(Req_Seq) > int.Z (map_get lastSeqM req.(Req_CID)).1)%Z⌝ ∗
           "%" ∷ ⌜reply'.(Rep_Stale) = false⌝ ∗
           "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(Req_CID):=req.(Req_Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝ ∗
           "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM ∗
           ((⌜reply'.(Rep_Stale) = true⌝ ∗ (RPCServer_own_ghost γrpc lastSeqM lastReplyM ={⊤}=∗ RPCRequestStale γrpc req ∗ RPCServer_own_ghost γrpc lastSeqM lastReplyM )) ∨
             (RPCServer_own_ghost γrpc lastSeqM lastReplyM ={⊤}=∗ RPCReplyReceipt γrpc req reply'.(Rep_Ret) ∗ RPCServer_own_ghost γrpc lastSeqM lastReplyM ))) ∗

    "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
}}}
.
Proof.
  iIntros (?) "#Hisrpc". iIntros (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  repeat wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  iNamed "Hreply".
  wp_storeField.
  wp_apply (wp_and ok (int.Z req.(Req_Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }
  rewrite bool_decide_decide.
  destruct (decide (ok ∧ int.Z req.(Req_Seq) ≤ int.Z v)%Z) as [ [Hok Hineq]|Hmiss].
  { (* Cache hit *)
    destruct ok; last done. clear Hok. (* ok = false *)
    wp_pures.
    apply map_get_true in HSeqMapGet.
    destruct bool_decide eqn:Hineqstrict.
    - wp_pures.
      apply bool_decide_eq_true in Hineqstrict.
      wp_storeField.
      iApply ("HΦ" $! _ (Build_RPCReply _ _)).
      iFrame "HReplyOwnStale HReplyOwnRet HlastReplyMap".
      iRight.
      iFrame.
      iSplitL ""; first done.
      iLeft.
      iSplitL ""; first done.
      iIntros "Hsrpc".
      iMod (smaller_seqno_stale_fact with "[$] Hsrpc") as "[Hsrpc #Hstale]"; eauto.
    - wp_pures.
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      iApply ("HΦ" $! _ (Build_RPCReply _ _)).
      iFrame "HReplyOwnStale HReplyOwnRet HlastReplyMap".
      iRight.
      iFrame.
      iSplitL ""; first done.
      iRight.
      iIntros "Hsrpc".
      iMod (server_replies_to_request with "[$] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      apply bool_decide_eq_false in Hineqstrict.
      assert (int.Z req.(Req_Seq) = int.Z v) by lia.
      naive_solver.
  }
  { (* Cache miss *)
    wp_pures.
    apply not_and_r in Hmiss.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(Req_Seq) (#req.(Req_Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_seq.
    iApply ("HΦ" $! _ (Build_RPCReply _ _)).
    iFrame "HReplyOwnStale HReplyOwnRet HlastReplyMap".
    iLeft.
    iFrame.
    iSplitL ""; first done.
    iPureIntro.
    split; last naive_solver.

    rewrite HSeqMapGet; simpl.
    destruct Hmiss as [Hnok|Hineq].
    - destruct ok; first done.
      apply map_get_false in HSeqMapGet as [_ HSeqMapGet].
      rewrite HSeqMapGet.
      simpl.
      word.
    - word.
  }
Qed.

(* This will alow handler functions using RPCServer__HandleRequest to establish is_rpcHandler *)
Lemma RPCServer__HandleRequest_spec (coreFunction:val) (sv:loc) γrpc γreq server_ctx server_ctx' rid args req_ptr rep_ptr PreCond PostCond lastSeqM lastReplyM :
    (* ∀ Ψ, (∀ (r:u64), ▷ PostCond r -∗ Ψ #r) (WP coreFunction (into_val.to_val args)%V {{ Ψ }}). *)

(
  {{{
       server_ctx ∗ ▷ PreCond
  }}}
    coreFunction (into_val.to_val args)%V
  {{{
       (r:u64), RET #r; server_ctx' ∗ ▷ PostCond r
  }}}
  ) -∗

{{{
     "#His_req" ∷ is_RPCRequest γrpc γreq PreCond PostCond rid ∗
     "#Hread_req" ∷ RPCRequest_own_ro req_ptr rid args ∗
     "Hrpc_vol" ∷ RPCServer_own_vol sv γrpc lastSeqM lastReplyM ∗
     "Hrpc_ghost" ∷ RPCServer_own_ghost γrpc lastSeqM lastReplyM ∗
     "Hreply" ∷ (∃ rep, RPCReply_own rep_ptr rep) ∗
     "Hctx" ∷ server_ctx
}}}
  RPCServer__HandleRequest #sv coreFunction #req_ptr #rep_ptr
{{{
     reply, RET #();
     ∃ lastSeqM lastReplyM,
     RPCServer_own_vol sv γrpc lastSeqM lastReplyM ∗
     RPCServer_own_ghost γrpc lastSeqM lastReplyM ∗

     RPCReply_own rep_ptr reply ∗
     (⌜reply.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc rid ∨ RPCReplyReceipt γrpc rid reply.(Rep_Ret)) ∗

     (server_ctx ∨ server_ctx') (* If desired, could tie this to the update of the reply table *)
}}}.
Proof.
  iIntros "#HfCoreSpec !#" (Φ) "Hpre HΦ".
  iNamed "Hpre".
  iDestruct "Hreply" as (dummyReply) "Hreply".
  wp_lam.
  wp_pures.
  iNamed "Hrpc_vol".
  iNamed "Hread_req".
  repeat wp_loadField.
  wp_apply (CheckReplyTable_spec with "Hlinv [$HlastSeqMap $HlastReplyMap $Hreply]").
  { done. }
  iIntros (b reply) "HcheckTablePost".
  iNamed "HcheckTablePost".
  wp_if_destruct.
  {
    iApply wp_fupd.
    wp_pures.
    iApply "HΦ".
    iDestruct "Hcases" as "[[% _]|Hcases]"; first by exfalso.
    iNamed "Hcases".
    iExists _, _.
    iSplitL "HlastReplyMap HlastSeqMap HlastSeqOwn HlastReplyOwn".
    { iExists _, _. iFrame "∗#". done. }

    iFrame "Hreply".
    iDestruct "Hcases" as "[[% Hfupd]|Hfupd]".
    { (* Stale *)
      iMod ("Hfupd" with "Hrpc_ghost") as "[#Hstale $]".
      iFrame.
      iLeft.
      eauto.
    }
    { (* Receipt *)
      iMod ("Hfupd" with "Hrpc_ghost") as "[#Hreceipt $]".
      iFrame.
      iRight.
      eauto.
    }
  }
  {
    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".
    iMod (server_takes_request with "[] Hrpc_ghost") as "(Hγpre & HcorePre & Hprocessing)"; eauto.
    {
      apply Z.gt_lt.
      done.
    }
    wp_pures.
    repeat wp_loadField.
    wp_apply ("HfCoreSpec" with "[$HcorePre $Hctx]").
    iIntros (retval) "[Hsrv HcorePost]".
    iNamed "Hreply".
    wp_storeField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert _ _ lastReplyM _ retval (#retval) with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
    iMod (server_completes_request with "[] [] Hγpre HcorePost Hprocessing") as "[#Hreceipt Hsrpc] /="; eauto.
    {
      apply Z.gt_lt.
      done.
    }
    wp_pures.
    iApply ("HΦ" $! (Build_RPCReply _ _)).
    iExists _, _.
    iFrame "Hsrpc".
    iSplitL "HlastReplyMap HlastSeqMap HlastSeqOwn HlastReplyOwn".
    { iExists _, _. iFrame "∗#". }
    iFrame "HReplyOwnStale HReplyOwnRet".
    iFrame "Hsrv".
    iRight.
    iFrame "#".
  }
Qed.

Definition reqEncoded (req:RPCRequestID) (args:RPCValsC) (bs:list u8) : Prop :=
  int.nat req.(Req_Seq) > 0 ∧
  has_encoding bs [EncUInt64 req.(Req_CID);
                   EncUInt64 req.(Req_Seq);
                   EncUInt64 args.(U64_1);
                   EncUInt64 args.(U64_2)].

Theorem wp_rpcReqEncode (req_ptr:loc) (req:RPCRequestID) (args:RPCValsC) :
  {{{
    RPCRequest_own_ro req_ptr req args
  }}}
    rpcReqEncode #req_ptr
  {{{
    s (bs:list u8), RET (slice_val s);
    is_slice s u8T 1%Qp bs ∗
    ⌜reqEncoded req args bs⌝
  }}}.
Proof.
  iIntros (Φ) "#Hreq HΦ".
  iNamed "Hreq".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (e) "He".
  wp_loadField.
  replace (word.mul 4%Z 8%Z) with (U64 32); last first.
  {
    rewrite -word.ring_morph_mul.
    word.
  }
  wp_apply (wp_Enc__PutInt with "He"); first word.
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He"); first word.
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He"); first word.
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He"); first word.
  iIntros "He".
  wp_apply (wp_Enc__Finish with "He").
  iIntros (s bs) "(%Hhasenc & %Hlen & Hs)".
  wp_pures.
  iApply "HΦ".
  iFrame "Hs".
  iPureIntro. rewrite /reqEncoded.
  simpl in Hhasenc. eauto.
Qed.

Theorem wp_rpcReqDecode (s:Slice.t) (reqptr:loc) (bs:list u8) (req:RPCRequestID) (args:RPCValsC) q :
  {{{
    is_slice_small s u8T q bs ∗
    ⌜reqEncoded req args bs⌝ ∗
    reqptr ↦[struct.t RPCRequest.S] (#0, (#0, (#0, (#0, #()), #())))
  }}}
    rpcReqDecode (slice_val s) #reqptr
  {{{
    RET #();
    RPCRequest_own_ro reqptr req args
  }}}.
Proof.
  iIntros (Φ) "(Hs & %Henc & Hreq) HΦ".
  iDestruct (struct_fields_split with "Hreq") as "Hreq". iNamed "Hreq".
  wp_call.
  wp_apply (wp_new_dec with "Hs").
  { eapply Henc. }
  iIntros (d) "Hd".
  wp_apply (wp_Dec__GetInt with "Hd"). iIntros "Hd".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hd"). iIntros "Hd".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hd"). iIntros "Hd".
  wp_apply (wp_struct_fieldRef_mapsto with "Args"); first done.
  iIntros (fl) "[%Hfl Args]".
  wp_apply (wp_storeField_struct with "Args"); first auto.
  iIntros "Args".
  rewrite Hfl; clear Hfl fl.
  wp_apply (wp_Dec__GetInt with "Hd"). iIntros "Hd".
  wp_apply (wp_struct_fieldRef_mapsto with "Args"); first done.
  iIntros (fl) "[%Hfl Args]".
  iApply wp_fupd.
  wp_apply (wp_storeField_struct with "Args"); first auto.
  iIntros "Args".
  rewrite Hfl; clear Hfl fl.
  rewrite /=.
  iMod (readonly_alloc_1 with "CID") as "#CID".
  iMod (readonly_alloc_1 with "Seq") as "#Seq".
  iMod (readonly_alloc_1 with "Args") as "#Args".
  wp_pures.
  iApply "HΦ".
  destruct Henc as [Hseqpos Henc].
  iModIntro. iSplit; eauto.
Qed.

Definition replyEncoded (r:RPCReply) (bs:list u8) : Prop :=
  has_encoding bs [EncBool r.(Rep_Stale);
                   EncUInt64 r.(Rep_Ret)].

Theorem wp_rpcReplyEncode (reply_ptr:loc) (reply:RPCReply) :
  {{{
    RPCReply_own reply_ptr reply
  }}}
    rpcReplyEncode #reply_ptr
  {{{
    s (bs:list u8), RET (slice_val s);
    is_slice s u8T 1%Qp bs ∗
    ⌜replyEncoded reply bs⌝
  }}}.
Proof.
  iIntros (Φ) "Hreply HΦ".
  iNamed "Hreply".
  wp_call.
  wp_apply wp_new_enc.
  iIntros (e) "He".
  wp_loadField.
  wp_apply (wp_Enc__PutBool with "He").
  { admit. }
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He").
  { admit. }
  iIntros "He".
  wp_apply (wp_Enc__Finish with "He").
  iIntros (s bs) "(%Hhasenc & %Hlen & Hs)".
  wp_pures.
  iApply "HΦ".
  iFrame "Hs".
  iPureIntro. rewrite /replyEncoded.
  simpl in Hhasenc. eauto.
Admitted.

Theorem wp_rpcReplyDecode (s:Slice.t) (reply_ptr:loc) (bs:list u8) (reply:RPCReply) q (v0 : bool) (v1 : u64) :
  {{{
    is_slice_small s u8T q bs ∗
    ⌜replyEncoded reply bs⌝ ∗
    reply_ptr ↦[struct.t RPCReply.S] (#v0, (#v1, #()))
  }}}
    rpcReplyDecode (slice_val s) #reply_ptr
  {{{
    RET #();
    RPCReply_own reply_ptr reply
  }}}.
Proof.
  iIntros (Φ) "(Hs & %Henc & Hreply) HΦ".
  iDestruct (struct_fields_split with "Hreply") as "Hreply". iNamed "Hreply".
  wp_call.
  wp_apply (wp_new_dec with "Hs").
  { eapply Henc. }
  iIntros (d) "Hd".
  wp_apply (wp_Dec__GetBool with "Hd"). iIntros "Hd".
  wp_storeField.
  wp_apply (wp_Dec__GetInt with "Hd"). iIntros "Hd".
  wp_storeField.
  wp_pures.
  iApply "HΦ".
  iSplitL "Stale"; iFrame.
Qed.

(* TODO: add args to PreCond and PostCond here *)
Definition EncodedPre2 {X:Type} Pre : (X → list u8 → iProp Σ) :=
 (λ x reqData, ∃ req args, ⌜reqEncoded req args reqData⌝ ∗ Pre x req args)%I
.

Definition EncodedPost2 {X:Type} Post : (X → list u8 → list u8 → iProp Σ) :=
  (λ x reqData repData,
    ∃ req args reply, ⌜reqEncoded req args reqData⌝ ∗
                      ⌜replyEncoded reply repData⌝ ∗
                      Post x req args reply
                      )%I
.

(* This says an rpc handler has the given PreCond and PostCond; it does NOT say
   that the handler sits behind a reply table with the given Pre/Post. *)
Definition handler_is2 (X:Type) (host:string) (rpcid:u64) PreCond PostCond : iProp Σ :=
  handler_is X host rpcid (EncodedPre2 PreCond) (EncodedPost2 PostCond)
.

Definition is_rpcHandler2 {X:Type} f Pre Post : iProp Σ :=
  is_rpcHandler (X:=X) f (EncodedPre2 Pre) (EncodedPost2 Post)
.

Lemma wp_RemoteProcedureCall2 (cl_ptr req_ptr reply_ptr:loc) (host:string) (rpcid:u64) (req:RPCRequestID) args (reply:Reply64) X PreCond PostCond x:
handler_is2 X host rpcid PreCond PostCond -∗
{{{
  "#HargsPre" ∷ □ PreCond x req args ∗
  "#Hargs" ∷ RPCRequest_own_ro req_ptr req args ∗
  "Hreply" ∷ RPCReply_own reply_ptr reply ∗
  "HrpcOwn" ∷ grove_ffi.RPCClient_own cl_ptr host
}}}
  RemoteProcedureCall2 #cl_ptr #rpcid #req_ptr #reply_ptr
{{{ e, RET #e;
    (∃ reply',
    RPCReply_own reply_ptr reply' ∗
    grove_ffi.RPCClient_own cl_ptr host
    ∗ (⌜e = true⌝ ∨ ⌜e = false⌝
        ∗ PostCond x req args reply'))
}}}.
Proof.
  iIntros "#Hspec" (Φ) "!# Hpre HΦ".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  wp_apply (wp_rpcReqEncode with "Hargs").
  iIntros (reqSlice reqBs) "[HreqSlice %Hreqenc]".
  wp_pures.
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (rep_ptr) "Hrep_ptr".
  wp_pures.
  wp_apply (wp_RPCClient__RemoteProcedureCall with "[$HreqSlice $Hrep_ptr $HrpcOwn]").
  {
    iFrame "Hspec".
    iModIntro.
    iModIntro.
    iExists _,_; iFrame "HargsPre".
    done.
  }
  iIntros (errb rep_sl repData) "(Hrep_ptr & HrpcOwn & Hreq_sl & Hrep_sl & Hpost)".
  wp_pures.
  iDestruct "Hpost" as "[->|Hpost]".
  {
    wp_pures.
    iApply "HΦ".
    iExists _; iFrame.
    by iLeft.
  }
  iDestruct "Hpost" as "(-> & Hpost)".
  (* iMod "Hpost". *)
  iMod (later_exist_except_0 with "Hpost") as (req1) "Hpost".
  iMod (later_exist_except_0 with "Hpost") as (args1) "Hpost".
  iMod (later_exist_except_0 with "Hpost") as (reply1) "Hpost".
  iDestruct "Hpost" as "(>% & >% & Hpost)".

  iDestruct (is_slice_small_acc with "Hrep_sl") as "[Hrep_sl_small Hclose]".
  wp_pures.
  wp_load.
  wp_apply (wp_rpcReplyDecode with "[Hrep_sl_small Hreply]").
  {
    iFrame.
    iNamed "Hreply".
    iDestruct (struct_fields_split with "[HReplyOwnStale HReplyOwnRet]") as "$".
    {
      iFrame.
      done.
    }
    done.
  }
  iIntros "Hreply".
  wp_pures.
  iApply "HΦ".
  iExists reply1.
  iFrame.
  iRight.
  replace (req) with (req1); last first.
  {
    unfold reqEncoded in *.
    (* TODO: injectivity *)
    admit.
  }
  replace (args) with (args1); last first.
  {
    unfold reqEncoded in *.
    (* TODO: injectivity *)
    admit.
  }
  iFrame.
  done.
Admitted.

Lemma RPCClient__MakeRequest_spec {X:Type} (host:string) (rpcid:u64) cl_ptr args γrpc X PreCond PostCond (x:X):
  ∀ RawPreCond, handler_is2 X host rpcid RawPreCond (λ y req args reply, RPCRequestStale γrpc req ∨ RPCReplyReceipt γrpc req reply.(Rep_Ret)) -∗
□(∀ y req γreq, is_RPCRequest γrpc γreq (PreCond x args) (PostCond x args) req -∗ RawPreCond y req args) -∗
{{{
  PreCond x args ∗
  RPCClient_own cl_ptr host γrpc ∗
  is_RPCServer γrpc
}}}
  RPCClient__MakeRequest #cl_ptr #rpcid (into_val.to_val args)
{{{ (retv:u64), RET #retv; RPCClient_own cl_ptr host γrpc ∗ PostCond x args retv }}}.
Proof using Type*.
  iIntros (?) "#Hfspec #HfspecWand".
  iIntros (Φ) "!# [Hprecond [Hclerk #Hlinv]] Hpost".
  iDestruct "Hclerk" as (??) "[Hclerk_vol Hclerk_ghost]".
  iNamed "Hclerk_vol".
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (Hincr_safe).
  wp_seq.
  wp_loadField.
  wp_loadField.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (req_ptr) "Hreq".
  iDestruct (struct_fields_split with "Hreq") as "(HCID&HSeq&HArgs&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HArgs") as "#HArgs".
  wp_pures.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iMod (make_request {| Req_CID:=cid; Req_Seq:=seqno|} (PreCond x args) (PostCond x args) with "Hlinv Hclerk_ghost [$Hprecond]") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  wp_loadField.
  wp_storeField.
  wp_apply (wp_ref_to).
  { naive_solver. }
  iIntros (errb_ptr) "Herrb_ptr".
  wp_pures.
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', RPCReply_own reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }
  wp_forBreak.
  iDestruct "Herrb_ptr" as (err_old) "Herrb_ptr".
  wp_pures.
  iDestruct "Hreply" as (lockReply) "Hreply".
  wp_loadField.
  wp_apply (wp_RemoteProcedureCall2 with "Hfspec [$HrawClOwn $Hreply Hreqinv_init $HArgs]").
  {
    instantiate (1:=(Build_RPCRequestID _ _)).
    iFrame "HSeq HCID".
    iSplitR ""; last done.
    iModIntro.
    iApply "HfspecWand".
    iFrame "#".
  }

  iIntros (err) "HCallTryLockPost".
  iDestruct "HCallTryLockPost" as (lockReply') "(Hreply & HrawClOwn & [#Hre | [#Hre HCallPost]])".
  { (* No reply from CallTryLock *)
    iDestruct "Hre" as %->.
    wp_store.
    wp_load.
    wp_pures.
    iLeft. iSplitR; first done.
    iFrame; iFrame "#".
    iSplitL "Herrb_ptr"; eauto.
  }
  (* Got a reply from CallTryLock; leaving the loop *)
  iDestruct "Hre" as %->.
  wp_store.
  wp_load.
  iDestruct "HCallPost" as "[Hbad | #Hrcptstoro]"; simpl.
  {
    iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
    simpl in bad. replace (int.nat (word.add seqno 1))%nat with (int.nat seqno + 1)%nat in bad by word.
    lia.
  }
  iMod (get_request_post with "Hreqinv_init Hrcptstoro HγP") as "HP"; first done.
  wp_pures.
  iNamed "Hreply".
  iRight. iSplitR; first done.
  wp_seq.
  wp_loadField.
  iApply "Hpost".
  iFrame; iFrame "#".
  iExists _, (word.add seqno 1)%nat; iFrame.
  iExists _; iFrame.
  simpl.
  assert (int.nat seqno + 1 = int.nat (word.add seqno 1))%nat as <-; first by word.
  iPureIntro. lia.
Qed.

Lemma MakeRPCClient_spec γrpc (host : string) (cid : u64) :
  {{{ RPCClient_own_ghost γrpc cid 1 }}}
    MakeRPCClient #(str host) #cid
  {{{ cl, RET #cl; RPCClient_own cl host γrpc }}}.
Proof.
  iIntros (Φ) "Hclient_own HΦ". wp_lam.
  wp_pures.
  wp_apply (wp_MakeRPCClient).
  iIntros (cl_ptr) "HrawClOwn".
  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "(l_cid & l_seq & l_rawCl & _)".
  iApply "HΦ".
  iExists _, _. iFrame.
  iExists _; iFrame.
  by iPureIntro; word.
Qed.

Lemma MakeRPCServer_spec γrpc :
  {{{ is_RPCServer γrpc }}}
    MakeRPCServer #()
  {{{ sv, RET #sv; RPCServer_own_vol sv γrpc ∅ ∅ }}}
.
Proof.
  iIntros (Φ) "#Hrpcinv Hpost".
  wp_lam.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (l) "Hl".
  wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_lastSeq & l_lastReply & _)".

  iApply wp_fupd.
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (lastSeq) "HlastSeq".
  wp_storeField.
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (lastReply) "HlastReply".
  wp_storeField.
  iApply "Hpost".
  iExists _, _; iFrame "l_lastSeq ∗#".
  done.
Qed.

Definition is_rpcHandlerEncoded {X:Type} (f:val) PreCond PostCond : iProp Σ :=
  ∀ (x:X) args req req_ptr reply_ptr reply,
    {{{ "#HargsInv" ∷ (PreCond x args) ∗
        "#Hargs" ∷ RPCRequest_own_ro req_ptr req args ∗
        "Hreply" ∷ RPCReply_own reply_ptr reply
    }}} (* TODO: put this precondition into a defn *)
      f #req_ptr #reply_ptr
    {{{ RET #(); ∃ reply',
        RPCReply_own reply_ptr reply' ∗
        (⌜reply'.(Rep_Stale) = true⌝ ∗ PostCond x args reply'.(Rep_Ret))
    }}}
.

Lemma wp_ConjugateRpcFunc X (g:val) γrpc PreCond PostCond :
is_rpcHandlerEncoded (X:=X) g PreCond PostCond -∗
  {{{
       True
  }}}
    ConjugateRpcFunc g
  {{{
        (f:val), RET f; is_rpcHandler2 (X:=X) f PreCond PostCond
  }}}
.
Proof.
  iIntros "#Hgspec" (Φ) "!# Hpre HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  clear Φ.
  iIntros (???? Φ) "!# Hpre HΦ".
  wp_pures.
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (req_ptr) "Hreq".
  wp_apply (wp_allocStruct).
  { naive_solver. }
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iDestruct "Hpre" as "(Hreq_sl & Hrep_sl & Hpre)".
  iDestruct (is_slice_small_acc with "Hreq_sl") as "[Hreq_sl_small Hreq_close]".
  iDestruct "Hpre" as (???) "[% #His_req]".
  wp_apply (wp_rpcReqDecode with "[$Hreq_sl_small $Hreq]").
  { done. }
  iIntros "#Hreq_own".
  wp_pures.
  wp_apply ("Hgspec" $! _ _ _ _ _ (Build_RPCReply _ _) with "[$His_req $Hreq_own Hreply]").
  {
    iDestruct (struct_fields_split with "Hreply") as "Hreply".
    iNamed "Hreply".
    iFrame.
  }
  iIntros "Hpost".
  iDestruct "Hpost" as (reply) "[Hreply Hpost]".
  wp_pures.
  wp_apply (wp_rpcReplyEncode with "Hreply").
  iIntros (rep_sl' repData) "[Hrep_sl' %HrepEnc]".
  wp_store.
  iApply "HΦ".
  iFrame "Hrep_sl Hrep_sl'".
  iNext.
  iExists _, _, _; iFrame.
  iPureIntro.
  naive_solver.
Qed.

(* This tells us that it's safe to register the function as rpc with the desired spec *)
Lemma is_rpcHandler2_registration f host rpcid γrpc PreCond PostCond :
  is_rpcHandler2 f γrpc PreCond PostCond -∗
  handler_is2 host rpcid γrpc PreCond PostCond -∗
  (∃ Pre Post, handler_is host rpcid Pre Post ∗ is_rpcHandler f Pre Post).
Proof.
  iIntros.
  iExists _, _. iFrame "#".
Qed.

End rpc_proof.
