From Perennial.program_proof.lockservice Require Import lockservice nondet rpc.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From iris.algebra Require Import numbers.
From Coq.Structures Require Import OrdersTac.

Section rpc_types.
Context `{!heapG Σ}.

Print into_val.IntoVal.
#[refine] Global Instance u64_pair_val : into_val.IntoVal (u64*u64) :=
  {
  to_val := λ x, (#x.1, #x.2)%V ;
  IntoVal_def := (U64(0), U64(0)) ;
  IntoVal_inj := _
  }.
Admitted.

Definition read_request (args_ptr:loc) (a : @RPCRequest (u64 * u64)) : iProp Σ :=
    "#HSeqPositive" ∷ ⌜int.nat a.(rpc.Seq) > 0⌝
  ∗ "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Args"] (into_val.to_val a.(Args)))
  ∗ "#HArgsOwnCID" ∷ readonly (args_ptr ↦[RPCRequest.S :: "CID"] #a.(CID))
  ∗ "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Seq"] #a.(rpc.Seq))
.

Definition own_reply (reply_ptr:loc) (r : @RPCReply (u64)) : iProp Σ :=
    "HReplyOwnStale" ∷ reply_ptr ↦[RPCReply.S :: "Stale"] #r.(Stale)
  ∗ "HReplyOwnRet" ∷ reply_ptr ↦[RPCReply.S :: "Ret"] (into_val.to_val r.(Ret))
.

End rpc_types.

Section common_proof.

Context `{!heapG Σ}.
Axiom nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.

Lemma overflow_guard_incr_spec stk E (v:u64) : 
{{{ True }}}
  overflow_guard_incr #v @ stk ; E
{{{
     RET #(); ⌜((int.Z v) + 1 = int.Z (word.add v 1))%Z⌝
}}}.
Proof.
  iIntros (Φ) "_ Hpost".
  wp_lam. wp_pures.
  wp_forBreak_cond.
  wp_pures.
  destruct bool_decide eqn:Hineq.
  {
    apply bool_decide_eq_true in Hineq.
    wp_pures. iLeft. by iFrame.
  }
  {
    apply bool_decide_eq_false in Hineq.
    wp_pures. iRight. iSplitR; first done.
    iApply "Hpost". iPureIntro.
    assert (int.Z (word.add v 1) >= int.Z v)%Z by lia.
    destruct (bool_decide ((int.Z v) + 1 < 2 ^ 64 ))%Z eqn:Hnov.
    {
      apply bool_decide_eq_true in Hnov.
      word.
    }
    apply bool_decide_eq_false in Hnov.
    assert (int.Z v + (int.Z 1) >= 2 ^ 64)%Z.
    { replace (int.Z 1)%Z with (1)%Z by word. lia. }
    apply sum_overflow_check in H0.
    contradiction.
  }
Qed.

Context `{!rpcG Σ u64}.

Definition RPCServer_mutex_inv (sv:loc) (γrpc:rpc_names) (server_own_core:iProp Σ): iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 u64),
      "HlastSeqOwn" ∷ sv ↦[RPCServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ sv ↦[RPCServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM) (* TODO: Probably should get better naming for this *)
    ∗ server_own_core
.

Definition mutexN : namespace := nroot .@ "lockservermutexN".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_rpcserver (sv_ptr:loc) γrpc server_own_core: iProp Σ :=
  ∃ (mu_ptr:loc),
      "Hlinv" ∷ is_RPCServer γrpc
    ∗ "Hmu_ptr" ∷ readonly(sv_ptr ↦[RPCServer.S :: "mu"] #mu_ptr)
    ∗ "Hmu" ∷ is_lock mutexN #mu_ptr (RPCServer_mutex_inv sv_ptr γrpc server_own_core)
.

Definition Request64 := @RPCRequest (u64 * u64). (* TODO: rename these *)
Definition Reply64 := @RPCReply (u64).

Lemma CheckReplyTable_spec (reply_ptr:loc) (req:Request64) (reply:Reply64) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜int.nat req.(rpc.Seq) > 0⌝
    ∗ "#Hrinv" ∷ is_RPCServer γrpc
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
CheckReplyTable #lastSeq_ptr #lastReply_ptr #req.(CID) #req.(rpc.Seq) #reply_ptr
{{{
     v, RET v; ∃(b:bool) (reply':Reply64), "Hre" ∷ ⌜v = #b⌝
    ∗ "Hreply" ∷ own_reply reply_ptr reply'
    ∗ "Hcases" ∷ ("%" ∷ ⌜b = false⌝
         ∗ "%" ∷ ⌜(int.Z req.(rpc.Seq) > int.Z (map_get lastSeqM req.(CID)).1)%Z⌝
         ∗ "%" ∷ ⌜reply'.(Stale) = false⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(CID):=req.(rpc.Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
         ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req)
          ∨ RPCReplyReceipt γrpc req reply'.(Ret)))

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
  wp_apply (wp_and ok (int.Z req.(rpc.Seq) ≤ int.Z v)%Z).
  { wp_pures. by destruct ok. }
  { iIntros "_". wp_pures. done. }
  rewrite bool_decide_decide.
  destruct (decide (ok ∧ int.Z req.(rpc.Seq) ≤ int.Z v)%Z) as [ [Hok Hineq]|Hmiss].
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
      iExists {| Stale:=true; Ret:=_ |}.
      iFrame; iFrame "#".
      iSplitL ""; eauto.
    - wp_pures.
      assert (v = req.(rpc.Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (int.Z req.(rpc.Seq) = int.Z v) by lia; word.
      }
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      iMod (server_replies_to_request with "[Hrinv] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      wp_storeField.
      iApply "Hpost".
      iExists true. iExists {|Stale:=false; Ret:=reply_v |}.
      iFrame; iFrame "#". eauto.
  }
  { (* Cache miss *)
    wp_pures.
    apply not_and_r in Hmiss.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(rpc.Seq) (#req.(rpc.Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_seq.
    iApply "Hpost".
    iExists false. iExists {| Stale:=false; Ret:=reply.(Ret)|}.
    iFrame; iFrame "#".
    iSplitL ""; eauto.
    iLeft. iFrame. iPureIntro.
    split; eauto. split; eauto. injection HSeqMapGet as <- Hv. simpl.
    destruct Hmiss as [Hnok|Hineq].
    - destruct ok; first done.
      destruct (lastSeqM !! req.(CID)); first done.
      simpl. word.
    - word.
  }
Qed.

Lemma RPCServer__HandlRequest_spec (coreFunction:val) (sv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) γrpc γPost server_own_core PreCond PostCond :

(
∀ (args':u64*u64),
{{{ 
     server_own_core ∗ PreCond args'
}}}
  coreFunction (into_val.to_val args')
{{{
   v, RET v; server_own_core
      ∗ (∃r:u64, ⌜v = into_val.to_val r⌝ ∗ PostCond args' r)
}}}
)

-∗

{{{
  "#Hls" ∷ is_rpcserver sv γrpc server_own_core
  ∗ "#HreqInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req
  ∗ "#Hreq" ∷ read_request req_ptr req
  ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  RPCServer__HandleRequest #sv coreFunction #req_ptr #reply_ptr
{{{ RET #false; ∃ reply':Reply64, own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req)
  ∨ RPCReplyReceipt γrpc req reply'.(Ret))
}}}.
Proof.
  iIntros "#HfCoreSpec" (Φ) "!# Hpre Hpost".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  iNamed "Hls".
  wp_loadField.
  wp_apply (acquire_spec mutexN #mu_ptr _ with "Hmu").
  iIntros "(Hlocked & Hlsown)".
  iNamed "Hreq"; iNamed "Hreply".
  wp_seq.
  repeat wp_loadField.
  iNamed "Hlsown".
  iDestruct "HSeqPositive" as %HSeqPositive.
  repeat wp_loadField.
  wp_apply (CheckReplyTable_spec with "[-Hpost Hlocked Hlsown HlastSeqOwn HlastReplyOwn]"); first iFrame.
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
    wp_apply (release_spec mutexN #mu_ptr _ with "[-Hreply Hpost Hcases]"); try iFrame "Hmu Hlocked"; eauto.
    { iNext. iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "Hpost".
    iExists reply'.
    iFrame.
  }
  {
    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".
    iMod (server_takes_request with "[] [Hsrpc]") as "[HcorePre Hprocessing]"; eauto.
    wp_pures.
    repeat wp_loadField.
    wp_apply ("HfCoreSpec" with "[$Hlsown $HcorePre]"); eauto.
    iIntros (retval) "[Hsrv HcorePost]".
    iNamed "Hreply".
    iDestruct "HcorePost" as (r ->) "HcorePost".
    wp_storeField.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapInsert _ _ lastReplyM _ r (into_val.to_val r) with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
    iMod (server_completes_request with "[] [] HcorePost Hprocessing") as "[#Hreceipt Hsrpc] /="; eauto.
    wp_seq.
    wp_loadField.
    wp_apply (release_spec mutexN #mu_ptr _ with "[-HReplyOwnStale HReplyOwnRet Hpost]"); try iFrame "Hmu Hlocked".
    { iNext. iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "Hpost".
    iExists {|Stale:=false; Ret:=r |}. rewrite H1. iFrame; iFrame "#".
  }
Qed.

Lemma RemoteProcedureCall_spec (sv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) (f:val) (fname:string) server_own_core PreCond PostCond γrpc γPost :
(∀ (req_ptr' reply_ptr' : loc) (req':RPCRequest) 
   (reply' : Reply64) (γrpc' : rpc_names) (γPost' : gname),
{{{ "#HargsInv" ∷ is_RPCRequest γrpc' γPost' PreCond PostCond req'
    ∗ "#Hargs" ∷ read_request req_ptr' req'
    ∗ own_reply reply_ptr' reply'
}}}
  f #req_ptr' #reply_ptr'
{{{ RET #false; ∃ reply'',
    own_reply reply_ptr' reply''
        ∗ (⌜reply''.(Stale) = true⌝ ∗ RPCRequestStale γrpc' req'
               ∨ RPCReplyReceipt γrpc' req' reply''.(Ret)
             )
}}}
)
      -∗
{{{ "#Hls" ∷ is_rpcserver sv γrpc server_own_core
    ∗ "#HargsInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req
    ∗ "#Hargs" ∷ read_request req_ptr req
    ∗ own_reply reply_ptr reply
}}}
  RemoteProcedureCall f #req_ptr #reply_ptr
{{{ e, RET e;
    (∃ reply',
    own_reply reply_ptr reply' 
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝
        ∗ (⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req
               ∨ RPCReplyReceipt γrpc req reply'.(Ret)
             )))
}}}.
Proof.
  iIntros "#Hspec" (Φ) "!# Hpre Hpost".
  iNamed "Hpre".
  wp_rec.
  simpl.
  wp_let.
  wp_let.
  wp_apply wp_fork.
  {
    wp_apply (wp_allocStruct); first by eauto.
    iIntros (l) "Hl".
    iDestruct (struct_fields_split with "Hl") as "[HStale HRet]".
    iNamed "HStale"; iNamed "HRet".
    wp_let. wp_pures.
    (* Set up loop invariant *)
    iAssert (∃ reply, (own_reply l reply))%I with "[Stale Ret]" as "Hreply".
    { iExists {| Stale:=false; Ret:=_ |}. iFrame. }
    wp_forBreak. wp_pures.
    iDestruct "Hreply" as (reply') "Hreply".
    wp_apply ("Hspec" with "[-]").
    { iFrame "#∗". }
    iIntros "fPost".
    wp_seq. iLeft. iSplitR; first done.
    iDestruct "fPost" as (reply'') "[Hreply fPost]".
    iExists _. done.
  }
  wp_seq.
  wp_apply (nondet_spec).
  iIntros (choice) "[Hv|Hv]"; iDestruct "Hv" as %->.
  {
    wp_pures.
    wp_apply ("Hspec" with "[$HReplyOwnStale $HReplyOwnRet]"); eauto; try iFrame "#".
    iDestruct 1 as (reply') "[Hreply fPost]".
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

Definition Clerk__Function (f:val) (fname:string) : val :=
  rec: fname "ck" "lockname" :=
    overflow_guard_incr (struct.loadF Clerk.S "seq" "ck");;
    let: "args" := ref_to (refT (struct.t argty_to_adesc)) (struct.new argty_to_adesc [
      "Args" ::= "lockname";
      "CID" ::= struct.loadF Clerk.S "cid" "ck";
      "Seq" ::= struct.loadF Clerk.S "seq" "ck"
    ]) in
    struct.storeF Clerk.S "seq" "ck" (struct.loadF Clerk.S "seq" "ck" + #1);;
    let: "errb" := ref_to boolT #false in
    let: "reply" := struct.alloc retty_to_rdesc (zero_val (struct.t retty_to_rdesc)) in
    Skip;;
    (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
      "errb" <-[boolT] f (struct.loadF Clerk.S "primary" "ck") (![refT (struct.t argty_to_adesc)] "args") "reply";;
      (if: (![boolT] "errb" = #false)
      then Break
      else Continue));;
    struct.loadF retty_to_rdesc "Ret" "reply".

Definition own_clerk (ck:val) (srv:loc) (γrpc:rpc_names) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid cseqno : u64),
    "%" ∷ ⌜ck = #ck_l⌝
    ∗ "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ "Hseq" ∷ ck_l ↦[Clerk.S :: "seq"] #cseqno
    ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
    ∗ "Hcrpc" ∷ RPCClient_own γrpc cid cseqno
.

Lemma Clerk_Function_spec (f:val) (fname:string) ck (srv:loc) (args:u64) γrpc PreCond PostCond :
¬(fname = "ck") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "errb") -> ¬(fname = "lockname")
->
(∀ (srv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) γrpc' γPost',
{{{ "#Hls" ∷ is_server srv γrpc'
    ∗ "#HargsInv" ∷ is_RPCRequest γrpc' γPost' PreCond PostCond req
    ∗ "#Hargs" ∷ read_request req_ptr req
    ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  f #srv #req_ptr #reply_ptr
{{{ e, RET e;
    (∃ reply', own_reply reply_ptr reply'
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝
        ∗ (⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc' req
               ∨ RPCReplyReceipt γrpc' req reply'.(Ret)
             )))
}}})
  -∗
  {{{
       PreCond args
      ∗ own_clerk ck srv γrpc
      ∗ is_server srv γrpc
  }}}
    (Clerk__Function f fname) ck (into_val.to_val args)
  {{{ v, RET v; ∃(retv:u64), ⌜v = #retv⌝ ∗ own_clerk ck srv γrpc ∗ PostCond args retv }}}.
Proof using Type*.
  intros Hne1 Hne2 Hne3 Hne4 Hne5.
  iIntros "#Hfspec" (Φ) "!# [Hprecond [Hclerk #Hsrv]] Hpost".
  iNamed "Hclerk".
  rewrite H.
  wp_lam.

  rewrite (@decide_False _ (fname = "ck")); last done.
  rewrite (@decide_False _ (fname = "reply")); last done.
  rewrite (@decide_False _ (fname = "args")); last done.
  rewrite (@decide_False _ (fname = "errb")); last done.
  rewrite (@decide_False _ (fname = "lockname")); last done.
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "args"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "reply"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "errb"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "lockname"))); eauto.
  2:{ split; eauto. injection. eauto. }

  wp_pures.
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (Hincr_safe).
  wp_seq.
  repeat wp_loadField.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (req_ptr) "Hreq".
  iDestruct (struct_fields_split with "Hreq") as "(HCID&HSeq&HArgs&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HArgs") as "#HArgs".
  wp_apply wp_ref_to; first eauto.
  iIntros (req_ptr_ptr) "Hreq_ptr".
  wp_let.
  wp_loadField.
  wp_binop.
  wp_storeField.
  wp_apply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  wp_let.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  wp_pures.
  iDestruct "Hsrv" as (mu_ptr) "Hsrv". iNamed "Hsrv".
  iMod (make_request {| Args:=args; CID:=cid; rpc.Seq:=cseqno|} PreCond PostCond with "[Hlinv] [Hcrpc] [Hprecond]") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Ret:=_; Stale:=false |}. iFrame. }
  wp_forBreak.
  iDestruct "Herrb_ptr" as (err_old) "Herrb_ptr".
  wp_load.
  wp_loadField.
  iDestruct "Hreply" as (lockReply) "Hreply".
  wp_apply ("Hfspec" with "[Hreply]").
  {
    iSplitL "".
    { iExists _. iFrame "#". }
    iFrame "#".
    iDestruct "Hreply" as "[Hreply rest]".
    eauto with iFrame.
  }

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
    simpl in bad. replace (int.nat (word.add cseqno 1)) with (int.nat cseqno + 1) in bad by word. lia.
  }
  iMod (get_request_post with "Hreqinv_init Hrcptstoro HγP") as "HP"; first done.
  wp_pures.
  iNamed "Hreply".
  iRight. iSplitR; first done.
  wp_seq.
  wp_loadField.
  iApply "Hpost".
  iExists lockReply'.(Ret); iFrame; iFrame "#".
  iSplitR; first done.
  unfold own_clerk.
  iExists _, _, (word.add cseqno 1)%nat; iFrame.
  simpl.
  iSplitL ""; first done.
  assert (int.nat cseqno + 1 = int.nat (word.add cseqno 1))%nat as <-; first by word.
  iPureIntro. lia.
Qed.

Definition name_neq (name:string) : Prop :=
¬(name = "ls") ∧ ¬(name = "req") ∧ ¬(name = "srv") ∧
¬(name = "ck") ∧ ¬(name = "args") ∧ ¬(name = "reply") ∧ ¬(name = "errb") ∧ ¬(name = "lockname") ∧
¬(name = "dummy_reply") 
.

Lemma Clerk__from_core (coreFunction:val) (serverName:string) (callName:string) (clerkName:string) ck (srv:loc) (args:u64) γrpc PreCond PostCond :
  name_neq clerkName ∧
  name_neq serverName ∧
  name_neq callName
->
(
∀ (srv':loc) (args':u64),
{{{ 
     Server_own_core srv' ∗ PreCond args'
}}}
  coreFunction #srv' (into_val.to_val args')
{{{
   v, RET v; Server_own_core srv'
      ∗ (∃r:u64, ⌜v = into_val.to_val r⌝ ∗ PostCond args' r)
}}}
)
-∗
{{{
     PreCond args
    ∗ own_clerk ck srv γrpc
    ∗ is_server srv γrpc
}}}
    (Clerk__Function (CallFunction (Server_Function coreFunction serverName) callName) clerkName) ck (into_val.to_val args)
  {{{ v, RET v; ∃(retv:u64), ⌜v = #retv⌝ ∗ own_clerk ck srv γrpc ∗ PostCond args retv }}}.
Proof using Type*.
  intros Hne.
  destruct Hne as [Hone Hne]; repeat destruct Hone as [? Hone].
  destruct Hne as [Hone2 Hne]; repeat destruct Hone2 as [? Hone2].
  repeat destruct Hne as [? Hne].
  iIntros "#HcoreSpec" (Φ) "!# Hpre Hpost".
  iApply (Clerk_Function_spec with "[] Hpre"); [done..| |done].
  iIntros "*". iApply CallFunction_spec; [done..|].
  iIntros "*". iApply Server_Function_spec; [done..|].
  eauto.
Qed.

End common_proof.
