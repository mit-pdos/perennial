From stdpp Require Import gmap.
From iris.algebra Require Import numbers.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.ffi Require Import grove_ffi.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.program_proof.lockservice Require Import lockservice_nocrash common_proof.
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

Definition read_request (args_ptr:loc) (req : RPCRequestID) (args:RPCValsC) : iProp Σ :=
    "%HSeqPositive" ∷ ⌜int.nat req.(Req_Seq) > 0⌝ ∗
    "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Args"] (into_val.to_val args)) ∗
    "#HArgsOwnCID" ∷ readonly (args_ptr ↦[RPCRequest.S :: "CID"] #req.(Req_CID)) ∗
    "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Seq"] #req.(Req_Seq))
.

Definition own_reply (reply_ptr:loc) (r : @RPCReply (u64)) : iProp Σ :=
    "HReplyOwnStale" ∷ reply_ptr ↦[RPCReply.S :: "Stale"] #r.(Rep_Stale)
  ∗ "HReplyOwnRet" ∷ reply_ptr ↦[RPCReply.S :: "Ret"] (into_val.to_val r.(Rep_Ret))
.

Definition RPCServer_mutex_inv (sv:loc) (γrpc:rpc_names) (server_own_core:iProp Σ): iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 u64),
      "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM) (* TODO: Probably should get better naming for this *)
    ∗ server_own_core
.

(* TODO: Rename these to something generic *)
Definition mutexN : namespace := nroot .@ "lockservermutexN".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_rpcserver (sv_ptr:loc) γrpc server_own_core: iProp Σ :=
  ∃ (mu_ptr:loc),
      "Hlinv" ∷ is_RPCServer γrpc
    ∗ "Hmu_ptr" ∷ readonly(sv_ptr ↦[RPCServer.S :: "mu"] #mu_ptr)
    ∗ "Hmu" ∷ is_lock mutexN #mu_ptr (RPCServer_mutex_inv sv_ptr γrpc server_own_core)
.

Definition Reply64 := @RPCReply (u64).

Definition own_rpcclient (cl_ptr:loc) (γrpc:rpc_names) : iProp Σ
  :=
  ∃ (cid cseqno : u64),
      "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ cl_ptr ↦[RPCClient.S :: "cid"] #cid
    ∗ "Hseq" ∷ cl_ptr ↦[RPCClient.S :: "seq"] #cseqno
    ∗ "Hcrpc" ∷ RPCClient_own γrpc cid cseqno
.

(* f is a rpcHandler if it satisfies this specification *)
Definition is_rpcHandler (f:val) γrpc args req PreCond PostCond : iProp Σ :=
  ∀ γreq req_ptr reply_ptr reply,
    {{{ "#HargsInv" ∷ is_RPCRequest γrpc γreq PreCond PostCond req
                    ∗ "#Hargs" ∷ read_request req_ptr req args
                    ∗ "Hreply" ∷ own_reply reply_ptr reply
    }}} (* TODO: put this precondition into a defn *)
      f #req_ptr #reply_ptr
    {{{ RET #false; ∃ reply',
        own_reply reply_ptr reply' ∗
        (⌜reply'.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc req ∨
           RPCReplyReceipt γrpc req reply'.(Rep_Ret))
    }}}
    .

Definition is_rpcHandlerHost (host:u64) (rpcid:u64) γrpc args req PreCond PostCond : iProp Σ :=
  ∃ (handlers : gmap u64 val) (f : val),
    "#Hhost" ∷ host [[rpcreg_gname]]↦ro handlers ∗
    "%Hrpcid" ∷ ⌜handlers !! rpcid = Some f⌝ ∗
    "#Hhandler" ∷ is_rpcHandler f γrpc args req PreCond PostCond.

Lemma is_rpcHandler_eta (e:expr) γrpc args req PreCond PostCond :
  □ (∀ v1 v2,
    WP subst "reply" v1 (subst "req" v2 e) {{ v, is_rpcHandler v γrpc args req PreCond PostCond }}) -∗
  is_rpcHandler
    (λ: "req" "reply", e (Var "req") (Var "reply"))
    γrpc args req PreCond PostCond.
Proof.
  iIntros "#He" (???? Φ) "!# Hpre HΦ".
  wp_pures. wp_bind (subst _ _ _).
  iApply (wp_wand with "He"). iIntros (f) "Hfhandler".
  iApply ("Hfhandler" with "Hpre"). done.
Qed.

Lemma CheckReplyTable_spec (reply_ptr:loc) (req:RPCRequestID) (reply:Reply64) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜int.nat req.(Req_Seq) > 0⌝
    ∗ "#Hrinv" ∷ is_RPCServer γrpc
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(Req_CID) #req.(Req_Seq) #reply_ptr
{{{
     v, RET v; ∃(b:bool) (reply':Reply64), "Hre" ∷ ⌜v = #b⌝
    ∗ "Hreply" ∷ own_reply reply_ptr reply'
    ∗ "Hcases" ∷ ("%" ∷ ⌜b = false⌝
         ∗ "%" ∷ ⌜(int.Z req.(Req_Seq) > int.Z (map_get lastSeqM req.(Req_CID)).1)%Z⌝
         ∗ "%" ∷ ⌜reply'.(Rep_Stale) = false⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(Req_CID):=req.(Req_Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
         ∗ ((⌜reply'.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc req)
          ∨ RPCReplyReceipt γrpc req reply'.(Rep_Ret)))

    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
}}}
.
Proof.
  iIntros (Φ) "Hpre Hpost".
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
      iMod (smaller_seqno_stale_fact with "[] Hsrpc") as "[Hsrpc #Hstale]"; eauto.
      wp_storeField.
      iApply "Hpost".
      iExists true.
      iExists {| Rep_Stale:=true; Rep_Ret:=_ |}.
      iFrame; iFrame "#".
      iSplitL ""; eauto.
    - wp_pures.
      assert (v = req.(Req_Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (int.Z req.(Req_Seq) = int.Z v) by lia; word.
      }
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      iMod (server_replies_to_request with "[Hrinv] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      wp_storeField.
      iApply "Hpost".
      iExists true. iExists {|Rep_Stale:=false; Rep_Ret:=reply_v |}.
      iFrame; iFrame "#". eauto.
  }
  { (* Cache miss *)
    wp_pures.
    apply not_and_r in Hmiss.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(Req_Seq) (#req.(Req_Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_seq.
    iApply "Hpost".
    iExists false. iExists {| Rep_Stale:=false; Rep_Ret:=reply.(Rep_Ret)|}.
    iFrame; iFrame "#".
    iSplitL ""; eauto.
    iLeft. iFrame. iPureIntro.
    split; eauto. split; eauto. injection HSeqMapGet as <- Hv. simpl.
    destruct Hmiss as [Hnok|Hineq].
    - destruct ok; first done.
      destruct (lastSeqM !! req.(Req_CID)); first done.
      simpl. word.
    - word.
  }
Qed.

(* This will alow handler functions using RPCServer__HandleRequest to establish is_rpcHandler *)
Lemma RPCServer__HandleRequest_spec (coreFunction:val) (sv:loc) γrpc server_own_core args req PreCond PostCond :
({{{ server_own_core ∗ PreCond }}}
  coreFunction (into_val.to_val args)%V
{{{ (r:u64), RET #r; server_own_core ∗ PostCond r }}}) -∗
{{{ is_rpcserver sv γrpc server_own_core }}}
  RPCServer__HandleRequest #sv coreFunction
{{{ f, RET f; is_rpcHandler f γrpc args req PreCond PostCond }}}.
Proof.
  iIntros "#HfCoreSpec" (Φ) "!# #Hls Hpost".
  wp_lam.
  wp_pures. iApply "Hpost". clear Φ.
  iIntros (???? Φ) "!# Hpre HΦ".
  iNamed "Hpre". iNamed "Hls".
  wp_loadField.
  wp_apply (acquire_spec mutexN #mu_ptr _ with "Hmu").
  iIntros "(Hlocked & Hlsown)".
  iNamed "Hargs"; iNamed "Hreply".
  wp_seq.
  repeat wp_loadField.
  iNamed "Hlsown".
  iDestruct "HSeqPositive" as %HSeqPositive.
  repeat wp_loadField.
  wp_apply (CheckReplyTable_spec with "[-HΦ Hlocked Hlsown HlastSeqOwn HlastReplyOwn HfCoreSpec]"); first iFrame.
  { iFrame "#". done. }
  iIntros (runCore) "HcheckCachePost".
  iDestruct "HcheckCachePost" as (b reply' ->) "HcachePost".
  iNamed "HcachePost".
  destruct b.
  {
    wp_pures.
    wp_loadField.
    iDestruct "Hcases" as "[[% _]|Hcases]"; first done.
    iNamed "Hcases".
    wp_apply (release_spec mutexN #mu_ptr _ with "[-Hreply HΦ Hcases]"); try iFrame "Hmu Hlocked"; eauto.
    { iNext. iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "HΦ".
    iExists reply'.
    iFrame.
  }
  {
    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".
    iMod (server_takes_request with "[] [Hsrpc]") as "(Hγpre & HcorePre & Hprocessing)"; eauto.
    {
      apply Z.gt_lt.
      done.
    }
    wp_pures.
    repeat wp_loadField.
    wp_apply ("HfCoreSpec" with "[$Hlsown $HcorePre]").
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
    wp_seq.
    wp_loadField.
    wp_apply (release_spec mutexN #mu_ptr _ with "[-HReplyOwnStale HReplyOwnRet HΦ]"); try iFrame "Hmu Hlocked".
    { iNext. iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "HΦ".
    iExists {|Rep_Stale:=false; Rep_Ret:=retval |}. rewrite H1. iFrame; iFrame "#".
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
    read_request req_ptr req args
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
  wp_apply (wp_Enc__PutInt with "He").
  { admit. }
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He").
  { admit. }
  iIntros "He".
  wp_loadField.
  wp_apply (wp_Enc__PutInt with "He").
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
  iPureIntro. rewrite /reqEncoded.
  simpl in Hhasenc. eauto.
Admitted.

Theorem wp_rpcReqDecode (s:Slice.t) (reqptr:loc) (bs:list u8) (req:RPCRequestID) (args:RPCValsC) q :
  {{{
    is_slice_small s u8T q bs ∗
    ⌜reqEncoded req args bs⌝ ∗
    reqptr ↦[struct.t RPCRequest.S] (#0, (#0, (#0, (#0, #()), #())))
  }}}
    rpcReqDecode (slice_val s) #reqptr
  {{{
    RET #();
    read_request reqptr req args
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
  iSplit; eauto.
Qed.

Definition replyEncoded (r:RPCReply) (bs:list u8) : Prop :=
  has_encoding bs [EncBool r.(Rep_Stale);
                   EncUInt64 r.(Rep_Ret)].

Theorem wp_rpcReplyEncode (reply_ptr:loc) (reply:RPCReply) :
  {{{
    own_reply reply_ptr reply
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
    own_reply reply_ptr reply
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

Lemma RemoteProcedureCall_spec (req_ptr reply_ptr:loc) (req:RPCRequestID)
                               args (reply:Reply64) (host:u64) (rpcid:u64)
                               PreCond PostCond γrpc γPost :
is_rpcHandlerHost host rpcid γrpc args req PreCond PostCond -∗
{{{
  "#HargsInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req ∗
  "#Hargs" ∷ read_request req_ptr req args ∗
  "Hreply" ∷ own_reply reply_ptr reply
}}}
  RemoteProcedureCall #host #rpcid #req_ptr #reply_ptr
{{{ e, RET e;
    (∃ reply',
    own_reply reply_ptr reply' 
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝
        ∗ (⌜reply'.(Rep_Stale) = true⌝ ∗ RPCRequestStale γrpc req
               ∨ RPCReplyReceipt γrpc req reply'.(Rep_Ret)
             )))
}}}.
Proof.
  iIntros "#Hspec" (Φ) "!# Hpre Hpost".
  iNamed "Hpre".
  wp_rec.
  simpl.
  wp_let.
  wp_let.
  wp_let.
  wp_apply (wp_rpcReqEncode with "Hargs").
  iIntros (reqSlice reqBs) "[HreqSlice %Hreqenc]".
  iDestruct (is_slice_to_small with "HreqSlice") as "HreqSlice".

Opaque is_slice_small.
  iDestruct "HreqSlice" as "[HreqSlice0 HreqSlice1]".

  wp_apply (wp_fork with "[HreqSlice1]").
  {
    iModIntro.
    wp_apply (wp_allocStruct); first by eauto.
    iIntros (l) "Hl".
    iDestruct (struct_fields_split with "Hl") as "[HStale HRet]".
    iNamed "HStale"; iNamed "HRet".
    wp_let. wp_pures.
    (* Set up loop invariant *)
    iAssert (∃ reply, (own_reply l reply))%I with "[Stale Ret]" as "Hreply".
    { iExists {| Rep_Stale:=false; Rep_Ret:=_ |}. iFrame. }
    iAssert (∃ q, is_slice_small reqSlice u8T q reqBs)%I with "[HreqSlice1]" as "HreqSlice1".
    { iExists _; iFrame. }
    wp_forBreak. wp_pures.
    iDestruct "Hreply" as (reply') "Hreply".

    iNamed "Hspec".
    wp_apply (wp_GetServer with "[$Hhost]"); eauto.
    wp_let.

    wp_apply (wp_allocStruct); first by eauto.
    iIntros (sreqptr) "Hsreqptr".
    wp_pures.

    iDestruct "HreqSlice1" as (q) "HreqSlice1".
    iDestruct "HreqSlice1" as "[HreqSlice10 HreqSlice11]".
    wp_apply (wp_rpcReqDecode with "[$HreqSlice10 $Hsreqptr]"); eauto.
    iIntros "Hargs_server".

    wp_apply ("Hhandler" with "[-HreqSlice11]").
    { iFrame "#∗". }
    iIntros "fPost".
    wp_seq. iLeft. iSplitR; first done.
    iDestruct "fPost" as (reply'') "[Hreply fPost]".
    iSplitL "Hreply".
    { iExists _. done. }
    iExists _. done.
  }
  wp_seq.
  wp_apply (nondet_spec).
  iIntros (choice) "[Hv|Hv]"; iDestruct "Hv" as %->.
  {
    wp_pures.

    iNamed "Hspec".
    wp_apply (wp_GetServer with "[$Hhost]"); eauto.
    wp_let.

    wp_apply (wp_allocStruct); first by eauto.
    iIntros (sreqptr) "Hsreqptr".
    wp_pures.

    wp_apply (wp_rpcReqDecode with "[$HreqSlice0 $Hsreqptr]"); eauto.
    iIntros "Hargs_server".

    wp_apply (wp_allocStruct); first by eauto.
    iIntros (sreplyptr) "Hsreplyptr".
    wp_pures.

    wp_apply ("Hhandler" with "[Hsreplyptr]").
    { iFrame "#".
      replace (#false) with (#(@Build_RPCReply u64 false (U64 0)).(Rep_Stale)) by reflexivity.
      iDestruct (struct_fields_split with "Hsreplyptr") as "Hsreplyptr". iNamed "Hsreplyptr".
      iSplitL "Stale". { iFrame. }
      iFrame.
    }
    iDestruct 1 as (reply') "[Hsreplyptr fPost]".
    wp_pures.

    wp_apply (wp_rpcReplyEncode with "Hsreplyptr").
    iIntros (reply_s reply_bs) "[Hreply_s %Hreply_bs]".

    iDestruct (is_slice_to_small with "Hreply_s") as "Hreply_s".

    wp_pures.
    wp_apply (wp_rpcReplyDecode with "[$Hreply_s Hreply]").
    { iSplit; eauto.
      iApply struct_fields_split.
      rewrite /struct_fields /struct.struct_big_fields_rec /=.
      iNamed "Hreply".
      iSplitL "HReplyOwnStale"; iFrame. done.
    }
    iIntros "Hreplydec".
    wp_pures.

    iApply "Hpost".
    iFrame.
    iExists _; iFrame.
    iRight.
    iSplitL ""; first done.
    iFrame.
  }
  {
    wp_pures.
    iApply "Hpost".
    iExists _; iFrame.
    by iLeft.
  }
Qed.

Lemma RPCClient__MakeRequest_spec (host:u64) (rpcid:u64) cl_ptr args γrpc PreCond PostCond :
(∀ req, is_rpcHandlerHost host rpcid γrpc args req PreCond PostCond) -∗
{{{
  PreCond ∗
  own_rpcclient cl_ptr γrpc ∗
  is_RPCServer γrpc
}}}
  RPCClient__MakeRequest #cl_ptr #host #rpcid (into_val.to_val args)
{{{ (retv:u64), RET #retv; own_rpcclient cl_ptr γrpc ∗ PostCond retv }}}.
Proof using Type*.
  iIntros "#Hfspec" (Φ) "!# [Hprecond [Hclerk #Hlinv]] Hpost".
  iNamed "Hclerk".
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
  wp_loadField.
  wp_binop.
  wp_storeField.
  wp_apply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  wp_let.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iMod (make_request {| Req_CID:=cid; Req_Seq:=cseqno|} PreCond PostCond with "[Hlinv] [Hcrpc] [Hprecond]") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }
  wp_forBreak.
  iDestruct "Herrb_ptr" as (err_old) "Herrb_ptr".
  wp_pures.
  iDestruct "Hreply" as (lockReply) "Hreply".
  wp_apply (RemoteProcedureCall_spec with "[] [Hreply]"); first done.
  { by iFrame "# ∗". }

  iIntros (err) "HCallTryLockPost".
  iDestruct "HCallTryLockPost" as (lockReply') "[Hreply [#Hre | [#Hre HCallPost]]]".
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
  iDestruct "HCallPost" as "[ [_ Hbad] | #Hrcptstoro]"; simpl.
  {
    iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
    simpl in bad. replace (int.nat (word.add cseqno 1))%nat with (int.nat cseqno + 1)%nat in bad by word.
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
  iExists _, (word.add cseqno 1)%nat; iFrame.
  simpl.
  assert (int.nat cseqno + 1 = int.nat (word.add cseqno 1))%nat as <-; first by word.
  iPureIntro. lia.
Qed.

Lemma MakeRPCClient_spec γrpc (cid : u64) :
  {{{ RPCClient_own γrpc cid 1 }}}
    MakeRPCClient #cid
  {{{ cl, RET #cl; own_rpcclient cl γrpc }}}.
Proof.
  iIntros (Φ) "Hclient_own Hpost". wp_lam.
  wp_apply wp_allocStruct; first by eauto.
  iIntros (l) "Hl".
  iDestruct (struct_fields_split with "Hl") as "(l_cid & l_seq & _)".
  iApply "Hpost".
  iExists _, _. iFrame.
  by iPureIntro; word.
Qed.

Lemma MakeRPCServer_spec server_own_core γrpc :
  {{{ is_RPCServer γrpc ∗ RPCServer_own γrpc ∅ ∅ ∗ server_own_core }}}
    MakeRPCServer #()
  {{{ sv, RET #sv; is_rpcserver sv γrpc server_own_core }}}
.
Proof.
  iIntros (Φ) "[#Hrpcinv Hpre] Hpost".
  wp_lam.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (l) "Hl".
  wp_pures.
  iDestruct (struct_fields_split with "Hl") as "(l_mu & l_lastSeq & l_lastReply & _)".

  iApply wp_fupd.
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (lastSeq) "HlastSeq".
  wp_storeField.
  wp_apply (wp_NewMap u64 (t:=uint64T)). iIntros (lastReply) "HlastReply".
  wp_storeField.
  wp_apply (newlock_spec _ _ (RPCServer_mutex_inv _ _ server_own_core) with "[-Hpost l_mu]").
  { iNext.
    iExists _, _, _, _. iFrame "l_lastSeq l_lastReply".
    iFrame. }
  iIntros (lk) "Hlock".
  iDestruct (is_lock_flat with "Hlock") as %[lock ->].
  wp_storeField.
  iMod (readonly_alloc_1 with "l_mu") as "l_mu".
  iApply "Hpost".
  by iExists _; iFrame "# ∗".
Qed.

End rpc_proof.
