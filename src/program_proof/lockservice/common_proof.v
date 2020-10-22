From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map nondet rpc.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map fmcounter.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From iris.algebra Require Import numbers.
From Coq.Structures Require Import OrdersTac.
Section rpc_types.
Context `{!heapG Σ}.

Class RPCArgs (A:Type) :=
  {
  RPCArgs_IntoVal:> into_val.IntoVal A ;
  a_ty : ty;
  }.

Class RPCReturn (R:Type) :=
  {
  RPCReturn_Inhabited:> Inhabited R ;
  RPCReturn_IntoVal:> into_val.IntoVal R ;
  r_ty : ty ;
  r_has_zero:has_zero r_ty ;
  r_default: R;
  r_default_is_zero: (into_val.to_val r_default) = zero_val r_ty;
  }.

Context {A:Type}.
Context {A_RPCArgs:RPCArgs A}.
Context {R:Type}.
Context {R_RPCReturn:RPCReturn R}.

Definition retty_to_rdesc :=
  [("Stale", boolT) ; ("Ret", r_ty) ].

Definition argty_to_adesc :=
  [("CID", uint64T) ; ("Seq", uint64T) ; ("Args", a_ty) ].

Definition read_request (args_ptr:loc) (a : @RPCRequest A) : iProp Σ :=
  let req_desc := argty_to_adesc in
    "#HSeqPositive" ∷ ⌜int.nat a.(rpc.Seq) > 0⌝
  ∗ "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[req_desc :: "Args"] (into_val.to_val a.(Args)))
  ∗ "#HArgsOwnCID" ∷ readonly (args_ptr ↦[req_desc :: "CID"] #a.(CID))
  ∗ "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[req_desc :: "Seq"] #a.(rpc.Seq))
.

Definition own_reply (reply_ptr:loc) (r : @RPCReply R) : iProp Σ :=
  let reply_desc := retty_to_rdesc in
    "HReplyOwnStale" ∷ reply_ptr ↦[reply_desc :: "Stale"] #r.(Stale)
  ∗ "HReplyOwnRet" ∷ reply_ptr ↦[reply_desc :: "Ret"] (into_val.to_val r.(Ret))
.

End rpc_types.

Section lockservice_common_proof.

Context `{!heapG Σ}.

Axiom nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.

Lemma overflow_guard_incr_spec stk E (v:u64) : 
{{{ True }}}
  overflow_guard_incr #v @ stk ; E
{{{
     RET #(); ⌜((int.val v) + 1 = int.val (word.add v 1))%Z⌝
}}}.
Proof.
  iIntros (Φ) "Hpre Hpost".
  wp_lam. wp_pures.
  wp_apply (wp_forBreak_cond
              (fun b => ((⌜b = true⌝ ∨ ⌜((int.val v) + 1 = int.val (word.add v 1))%Z⌝)
)) with "[] []")%I; eauto.
  {
    iIntros (Ψ). iModIntro.
    iIntros "_ HΨpost".
    wp_pures.
    destruct bool_decide eqn:Hineq.
    {
      apply bool_decide_eq_true in Hineq.
      wp_pures.
      iApply "HΨpost".
      iFrame; by iLeft.
    }
    {
      apply bool_decide_eq_false in Hineq.
      wp_pures.
      iApply "HΨpost". iFrame; iRight.
      iPureIntro.
      assert (int.val (word.add v 1) >= int.val v)%Z by lia.
      destruct (bool_decide ((int.val v) + 1 < 2 ^ 64 ))%Z eqn:Hnov.
      {
        apply bool_decide_eq_true in Hnov.
        word.
      }
      apply bool_decide_eq_false in Hnov.
      assert (int.val v + (int.val 1) >= 2 ^ 64)%Z.
      { replace (int.val 1)%Z with (1)%Z by word. lia. }
      apply sum_overflow_check in H0.
      contradiction.
    }
  }
  {
    iIntros "[ %| %]"; first discriminate.
    by iApply "Hpost".
  }
Qed.

Global Instance u64_RPCArgs : RPCArgs u64 := { a_ty := uint64T }.

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Print RPCReturn.
#[refine] Global Instance bool_RPCReply : RPCReturn bool := {r_ty := boolT; r_default := false }.
{ eauto. }
{ eauto. }
Defined.

Section common_defs.
Context `{R}.
Context `{rpc_args:RPCArgs A}.
Context {R_RPCReturn:RPCReturn R}.
Context `{fmcounter_mapG Σ}.
Context `{!inG Σ (exclR unitO)}.
Context `{!mapG Σ (u64*u64) (option R)}.
Context `{!mapG Σ (u64*u64) (option bool)}.
Context `{Server_own_core: loc -> iProp Σ}.

Definition Server_mutex_inv (srv:loc) (γrpc:RPC_GS) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM:gmap u64 R),
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own lastSeqM lastReplyM γrpc)
    ∗ Server_own_core srv
.

Definition replycacheinvN : namespace := nroot .@ "replyCacheInvN".
Definition mutexN : namespace := nroot .@ "lockservermutexN".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_server (srv_ptr:loc) γrpc: iProp Σ :=
  ∃ mu_ptr,
      "Hmuptr" ∷ readonly (srv_ptr ↦[LockServer.S :: "mu"] #mu_ptr)
    ∗ ( "Hlinv" ∷ inv replycacheinvN (ReplyCache_inv γrpc ) )
    ∗ ( "Hmu" ∷ is_lock mutexN #mu_ptr (Server_mutex_inv srv_ptr γrpc))
.
End common_defs.


Section common_proof.
Context `{rpc_args:RPCArgs A}.
Definition LockReply := @RPCReply bool.

Context `{fmcounter_mapG Σ}.
Context `{!inG Σ (exclR unitO)}.
Context `{!mapG Σ (u64*u64) (option bool)}.
Context `{Server_own_core: loc -> iProp Σ}.
Lemma LockServer__checkReplyCache_spec (srv reply_ptr:loc) (req:@RPCRequest A) (reply:LockReply) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜int.nat req.(rpc.Seq) > 0⌝
    ∗ "#Hrinv" ∷ (inv (replyCacheInvN) (ReplyCache_inv γrpc))
    ∗ "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own lastSeqM lastReplyM γrpc)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
LockServer__checkReplyCache #srv #req.(CID) #req.(rpc.Seq) #reply_ptr
{{{
     v, RET v; ∃(b:bool) (reply':LockReply), "Hre" ∷ ⌜v = #b⌝
    ∗ "Hreply" ∷ own_reply reply_ptr reply'
    ∗ "Hcases" ∷ ("%" ∷ ⌜b = false⌝
         ∗ "%" ∷ ⌜(int.val req.(rpc.Seq) > int.val (map_get lastSeqM req.(CID)).1)%Z⌝
         ∗ "%" ∷ ⌜reply'.(Stale) = false⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) (<[req.(CID):=req.(rpc.Seq)]>lastSeqM)
         ∨ 
         "%" ∷ ⌜b = true⌝
         ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
         ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale req γrpc)
          ∨ RPCReplyReceipt req reply'.(Ret) γrpc))

    ∗ "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own lastSeqM lastReplyM γrpc)
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

  iAssert
    (
{{{
⌜int.nat req.(rpc.Seq) > 0⌝
}}}
  if: #ok then #v ≥ #req.(rpc.Seq)
         else #false
{{{ ifr, RET ifr; ∃b:bool, ⌜ifr = #b⌝
  ∗ ((⌜b = false⌝ ∗ ⌜int.nat v < int.nat req.(rpc.Seq)⌝)
      ∨
     (⌜b = true⌝ ∗  ⌜(int.val req.(rpc.Seq) ≤ int.val v ∧ ok=true)%Z⌝)
    )
}}}
    )%I as "Htemp".
  {
    iIntros (Ψ). iModIntro.
    iIntros "HΨpre HΨpost".
    iDestruct "HΨpre" as "%".
    destruct ok.
    { wp_pures.
      destruct bool_decide eqn:Hineq.
      - apply bool_decide_eq_true in Hineq.
        iApply "HΨpost". iExists true.
        iSplitL ""; first done.
        iRight. iFrame. by iPureIntro.
      - apply bool_decide_eq_false in Hineq.
        iApply "HΨpost". iExists false.
        iSplitL ""; first done.
        iLeft. iFrame. iSplitL ""; eauto.
        iPureIntro. lia.
    }
    {
      wp_pures.
      apply map_get_false in HSeqMapGet as [Hnone Hv]. rewrite Hv.
      iApply "HΨpost". iExists false.
      iSplitL ""; first done.
      iLeft. iSplitL ""; eauto.
    }
  }
  wp_apply "Htemp"; eauto.
  iIntros (ifr) "Hifr".
  iDestruct "Hifr" as (b ->) "Hifr".
  destruct b.
  { (* Cache hit *)
    wp_pures.
    iDestruct "Hifr" as "[[% _]|[_ Hineq ]]"; first discriminate.
    iDestruct "Hineq" as %[Hineq Hok].
    rewrite ->Hok in *.
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
        assert (int.val req.(rpc.Seq) = int.val v) by lia; word.
      }
      wp_loadField.
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
    iDestruct "Hifr" as "[[_ Hineq]|[% _ ]]"; last discriminate.
    iDestruct "Hineq" as %Hineq.
    wp_loadField.
    wp_apply (wp_MapInsert _ _ lastSeqM _ req.(rpc.Seq) (#req.(rpc.Seq)) with "HlastSeqMap"); eauto.
    iIntros "HlastSeqMap".
    wp_seq.
    iApply "Hpost".
    iExists false. iExists {| Stale:=false; Ret:=reply.(Ret)|}.
    iFrame; iFrame "#".
    iSplitL ""; eauto.
    iLeft. iFrame. iPureIntro.
    split; eauto. split; eauto. injection HSeqMapGet as <-.
    simpl. word.
  }
Qed.

Definition LockServer_Function {A:Type} {R:Type} {r_rpcret:RPCReturn R} {a_rpcargs:RPCArgs A} (coreFunction:val) (fname:string) : val :=
  rec: "LockServer__TryLock" "ls" "req" "reply" :=
    lock.acquire (struct.loadF LockServer.S "mu" "ls");;
    (if: LockServer__checkReplyCache "ls" (struct.loadF argty_to_adesc "CID" "req") (struct.loadF argty_to_adesc "Seq" "req") "reply"
    then
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false
    else
      struct.storeF retty_to_rdesc "Ret" "reply" (coreFunction "ls" (struct.loadF argty_to_adesc "Args" "req"));;
      MapInsert (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF argty_to_adesc "CID" "req") (struct.loadF retty_to_rdesc "Ret" "reply");;
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false).

Print Server_mutex_inv.

Lemma LockServer_Function_spec (coreFunction:val) (fname:string) (srv req_ptr reply_ptr:loc) (req:RPCRequest) (reply:LockReply) γrpc γPost PreCond PostCond :
(
∀ (srv':loc) (args':A),
{{{ 
     Server_own_core srv' ∗ ▷ PreCond args'
}}}
  coreFunction #srv' (into_val.to_val args')
{{{
   v, RET v; Server_own_core srv'
      ∗ (∃r:bool, ⌜v = into_val.to_val r⌝ ∗ PostCond args' r)
}}}
)

->

{{{
  "#Hls" ∷ is_server srv γrpc (Server_own_core:=Server_own_core)
  ∗ "#HreqInv" ∷ inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γPost)
  ∗ "#Hreq" ∷ read_request req_ptr req
  ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  (LockServer_Function coreFunction fname) #srv #req_ptr #reply_ptr
{{{ RET #false; ∃ reply':LockReply, own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale req γrpc)
  ∨ RPCReplyReceipt req reply'.(Ret) γrpc)
}}}.
Proof.
  intros HfCoreSpec.
  iIntros (Φ) "Hpre Hpost".
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
  Check LockServer__checkReplyCache_spec.
  Check lastReplyM.
  wp_apply (LockServer__checkReplyCache_spec with "[-Hpost Hlocked Hlsown]"); first iFrame.
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
    { iNext.  iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "Hpost".
    iExists reply'.
    iFrame.
  }
  {
    wp_pures.
    iDestruct "Hcases" as "[Hcases | [% _]]"; last discriminate.
    iNamed "Hcases".
    repeat wp_loadField.
    iMod (server_takes_request with "[] [] [Hsrpc]") as "[HcorePre Hprocessing]"; eauto.
    wp_apply (HfCoreSpec with "[$Hlsown $HcorePre]"); eauto.
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
    iExists {|Stale:=false; Ret:=r |}. rewrite H2. iFrame; iFrame "#".
  }
Qed.

(* Returns true iff server reported error or request "timed out" *)
Definition CallFunction {R} {r_rpcret:RPCReturn R} (f:val) (fname:string) : val :=
  rec: fname "srv" "args" "reply" :=
    Fork (let: "dummy_reply" := struct.alloc (retty_to_rdesc)  (zero_val (struct.t (retty_to_rdesc))) in
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            f "srv" "args" "dummy_reply";;
            Continue));;
    (if: nondet #()
    then f "srv" "args" "reply"
    else #true).

Lemma CallFunction_spec {R} {R_RPCReturn:RPCReturn R} (srv req_ptr reply_ptr:loc) (req:@RPCRequest A) (reply:@RPCReply R) (f:val) (fname:string) fPre fPost γrpc γPost :
¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ srv' args' lockArgs' γrpc' γPost', Persistent (fPre srv' args' lockArgs' γrpc' γPost'))
-> (∀ (srv' req_ptr' reply_ptr' : loc) (req':RPCRequest) 
   (reply' : @RPCReply R) (γrpc' : RPC_GS) (γPost' : gname),
{{{ fPre srv' req_ptr' req' γrpc' γPost'
    ∗ own_reply reply_ptr' reply'
}}}
  f #srv' #req_ptr' #reply_ptr'
{{{ RET #false; ∃ reply'',
    own_reply reply_ptr' reply''
    ∗ fPost req' reply'' γrpc'
}}}
)
      ->
{{{ "#HfPre" ∷ fPre srv req_ptr req γrpc γPost ∗ "Hreply" ∷ own_reply (R:=R) reply_ptr reply }}}
  (CallFunction f fname) #srv #req_ptr #reply_ptr
{{{ e, RET e;
    (∃ reply',
    own_reply reply_ptr reply' 
        ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ fPost req reply' γrpc))
}}}.
Proof.
  intros Hpers Hne1 Hne2 Hne3 Hne4 Hspec.
  iIntros (Φ) "Hpre Hpost".
  iNamed "Hpre".
  wp_rec.
  rewrite (@decide_False _ (fname = "srv")); last done.
  rewrite (@decide_False _ (fname = "reply")); last done.
  rewrite (@decide_False _ (fname = "dummy_reply")); last done.
  rewrite (@decide_False _ (fname = "args")); last done.
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "args"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "reply"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "dummy_reply"))); eauto.
  2:{ split; eauto. injection. eauto. }
  simpl.
  wp_let.
  wp_let.
  wp_apply wp_fork.
  {
    Hint Resolve r_has_zero : core.
    wp_apply (wp_allocStruct); first eauto.
    { assert (has_zero r_ty); eauto. }
    iIntros (l) "Hl".
    iDestruct (struct_fields_split with "Hl") as "[HStale HRet]".
    iNamed "HStale"; iNamed "HRet".
    wp_let. wp_pures.
    wp_apply (wp_forBreak
                (fun b => ⌜b = true⌝∗
                                   ∃ reply, (own_reply l reply)
                )%I with "[] [Stale Ret]");
             try eauto.
    {
    iIntros (Ψ).
    iModIntro.
    iIntros "[_ Hpre] Hpost".
    iDestruct "Hpre" as (reply') "Hreply".
    wp_apply (Hspec with "[Hreply]"); eauto; try iFrame "#".

    iIntros "fPost".
    wp_seq.
    iApply "Hpost".
    iSplitL ""; first done.
    iDestruct "fPost" as (reply'') "[Hreply fPost]".
    iExists _. iFrame.
    }
    {
      iSplit; try done.
      iExists {| Stale:=false; Ret:=r_default |}.
      iFrame. rewrite r_default_is_zero. done.
    }
  }
  wp_seq.
  wp_apply (nondet_spec).
  iIntros (choice) "[Hv|Hv]"; iDestruct "Hv" as %->.
  {
    wp_pures.
    wp_apply (Hspec with "[$Hreply]"); eauto; try iFrame "#".
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
    iExists _; iFrame "Hreply".
    by iLeft.
  }
Qed.

End common_proof.
End lockservice_common_proof.
