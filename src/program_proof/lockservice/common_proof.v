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
  iIntros (Φ) "Hpre Hpost".
  wp_lam. wp_pures.
  wp_apply (wp_forBreak_cond
              (fun b => ((⌜b = true⌝ ∨ ⌜((int.Z v) + 1 = int.Z (word.add v 1))%Z⌝)
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
  }
  {
    iIntros "[ %| %]"; first discriminate.
    by iApply "Hpost".
  }
Qed.

Global Instance u64_RPCArgs : RPCArgs u64 := { a_ty := uint64T }.

#[refine] Global Instance u64_RPCReply : RPCReturn u64 := {r_ty := uint64T; r_default := 0 }.
{ eauto. }
{ eauto. }
Defined.

Context `{!rpcG Σ u64}.
Context `{Server_own_core: loc -> iProp Σ}.

Definition Server_mutex_inv (srv:loc) (γrpc:rpc_names) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM:gmap u64 u64),
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
    ∗ Server_own_core srv
.

Definition mutexN : namespace := nroot .@ "lockservermutexN".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_server (srv_ptr:loc) γrpc: iProp Σ :=
  ∃ mu_ptr,
      "Hmuptr" ∷ readonly (srv_ptr ↦[LockServer.S :: "mu"] #mu_ptr)
    ∗ "Hlinv" ∷ is_RPCServer γrpc
    ∗ "Hmu" ∷ is_lock mutexN #mu_ptr (Server_mutex_inv srv_ptr γrpc)
.

Definition Request64 := @RPCRequest u64.
Definition Reply64 := @RPCReply u64.

Lemma LockServer__checkReplyCache_spec (srv reply_ptr:loc) (req:Request64) (reply:Reply64) γrpc (lastSeq_ptr lastReply_ptr:loc) lastSeqM lastReplyM :
{{{
     "%" ∷ ⌜int.nat req.(rpc.Seq) > 0⌝
    ∗ "#Hrinv" ∷ is_RPCServer γrpc
    ∗ "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own γrpc lastSeqM lastReplyM)
    ∗ ("Hreply" ∷ own_reply reply_ptr reply)
}}}
LockServer__checkReplyCache #srv #req.(CID) #req.(rpc.Seq) #reply_ptr
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

    ∗ "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
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
  unfold retty_to_rdesc.
  wp_storeField.
  wp_apply (wp_and ok (int.Z req.(rpc.Seq) ≤ int.Z v)%Z).
  { iApply wp_value. by destruct ok. }
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
    apply not_and_r in Hmiss.
    wp_loadField.
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

Definition Server_Function (coreFunction:val) (fname:string) : val :=
  rec: fname "ls" "req" "reply" :=
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

Lemma Server_Function_spec (coreFunction:val) (fname:string) (srv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) γrpc γPost PreCond PostCond :

¬(fname = "ls") -> ¬(fname = "req") -> ¬(fname = "reply") 
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
  "#Hls" ∷ is_server srv γrpc
  ∗ "#HreqInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req
  ∗ "#Hreq" ∷ read_request req_ptr req
  ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  (Server_Function coreFunction fname) #srv #req_ptr #reply_ptr
{{{ RET #false; ∃ reply':Reply64, own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req)
  ∨ RPCReplyReceipt γrpc req reply'.(Ret))
}}}.
Proof.
  intros Hne1 Hne2 Hne3.
  iIntros "#HfCoreSpec" (Φ) "!# Hpre Hpost".
  iNamed "Hpre".
  wp_lam.
  rewrite (@decide_False _ (fname = "ls")); last done.
  rewrite (@decide_False _ (fname = "reply")); last done.
  rewrite (@decide_False _ (fname = "req")); last done.
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "req"))); eauto.
  2:{ split; eauto. injection. eauto. }
  rewrite (@decide_True _ (BNamed fname ≠ <>%binder ∧ (BNamed fname ≠ BNamed "reply"))); eauto.
  2:{ split; eauto. injection. eauto. }
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

(* Returns true iff server reported error or request "timed out" *)
Definition CallFunction (f:val) (fname:string) : val :=
  rec: fname "srv" "args" "reply" :=
    Fork (let: "dummy_reply" := struct.alloc (retty_to_rdesc)  (zero_val (struct.t (retty_to_rdesc))) in
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            f "srv" "args" "dummy_reply";;
            Continue));;
    (if: nondet #()
    then f "srv" "args" "reply"
    else #true).

Lemma CallFunction_spec (srv req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) (f:val) (fname:string) PreCond PostCond γrpc γPost :
¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ (srv' req_ptr' reply_ptr' : loc) (req':RPCRequest) 
   (reply' : Reply64) (γrpc' : rpc_names) (γPost' : gname),
{{{ "#Hls" ∷ is_server srv' γrpc'
    ∗ "#HargsInv" ∷ is_RPCRequest γrpc' γPost' PreCond PostCond req'
    ∗ "#Hargs" ∷ read_request req_ptr' req'
    ∗ own_reply reply_ptr' reply'
}}}
  f #srv' #req_ptr' #reply_ptr'
{{{ RET #false; ∃ reply'',
    own_reply reply_ptr' reply''
        ∗ (⌜reply''.(Stale) = true⌝ ∗ RPCRequestStale γrpc' req'
               ∨ RPCReplyReceipt γrpc' req' reply''.(Ret)
             )
}}}
)
      -∗
{{{ "#Hls" ∷ is_server srv γrpc
    ∗ "#HargsInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req
    ∗ "#Hargs" ∷ read_request req_ptr req
    ∗ own_reply reply_ptr reply
}}}
  (CallFunction f fname) #srv #req_ptr #reply_ptr
{{{ e, RET e;
    (∃ reply',
    own_reply reply_ptr reply' 
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝
        ∗ (⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req
               ∨ RPCReplyReceipt γrpc req reply'.(Ret)
             )))
}}}.
Proof.
  intros Hne1 Hne2 Hne3 Hne4.
  iIntros "#Hspec" (Φ) "!# Hpre Hpost".
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
    wp_apply ("Hspec" with "[Hreply]"); eauto; try iFrame "#".

    iIntros "fPost".
    wp_seq.
    iApply "Hpost".
    iSplitL ""; first done.
    iDestruct "fPost" as (reply'') "[Hreply fPost]".
    iExists _. done.
    }
    {
      iSplit; try done.
      iExists {| Stale:=false; Ret:=r_default |}.
      iFrame.
    }
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
  wp_apply (wp_forBreak
              (fun b =>
 (let req := ({| Args := args; CID:= cid; rpc.Seq := cseqno|}) in
    "#Hargs" ∷ read_request req_ptr req
  ∗ "#Hargsinv" ∷ is_RPCRequest γrpc γP PreCond PostCond req
  ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
  ∗ "Hseq" ∷ (ck_l ↦[Clerk.S :: "seq"] #(LitInt (word.add req.(rpc.Seq) 1)))
  ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
  ∗ "Hreq_ptr_ptr" ∷ req_ptr_ptr ↦[refT (uint64T * (uint64T * (uint64T * unitT))%ht)] #req_ptr
  ∗ "Herrb_ptr" ∷ (∃ (err:bool), errb_ptr ↦[boolT] #err)
  ∗ "Hreply" ∷ (∃ reply', own_reply reply_ptr reply' ∗ (⌜b = true⌝ ∨ PostCond args reply'.(Ret) ))
  ∗ "HγP" ∷ (⌜b = false⌝ ∨ own γP (Excl ()))
  ∗ ("Hcseq_own" ∷ RPCClient_own γrpc req.(CID) (word.add req.(rpc.Seq) 1))
  ∗ ("Hpost" ∷ ∀ v : val, (∃ retv : u64, ⌜v = #retv⌝ ∗ own_clerk #ck_l srv γrpc ∗ PostCond args retv) -∗ Φ v)
              ))%I with "[] [-]"); eauto.
  {
    iIntros (Ψ).
    iModIntro.
    iIntros "Hpre HΨpost".
    wp_lam.
    iNamed "Hpre".
    iDestruct "Herrb_ptr" as (err_old) "Herrb_ptr".
    wp_load.
    wp_loadField.
    iDestruct "Hreply" as (lockReply) "Hreply".
    (* WHY: Why does this destruct not work when inside the proof for CalTryLock's pre? *)
    wp_apply ("Hfspec" with "[Hreply]"); eauto.
    {
      iSplitL "".
      { iExists _. iFrame "#". }
      iFrame "#".
      iDestruct "Hreply" as "[Hreply rest]".
      iFrame.
    }

    iIntros (err) "HCallTryLockPost".
    iDestruct "HCallTryLockPost" as (lockReply') "[Hreply [#Hre | [#Hre HCallPost]]]".
    { (* No reply from CallTryLock *)
      iDestruct "Hre" as %->.
      wp_store.
      wp_load.
      wp_pures.
      iApply "HΨpost".
      iFrame; iFrame "#".
      iSplitL "Herrb_ptr"; eauto.
      iExists _; iFrame. by iLeft.
    }
    { (* Got a reply from CallTryLock *)
      iDestruct "Hre" as %->.
      wp_store.
      wp_load.
      iDestruct "HγP" as "[%|HγP]"; first discriminate.
      iDestruct "HCallPost" as "[ [_ Hbad] | #Hrcptstoro]"; simpl.
      {
        iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
        simpl in bad. replace (int.nat (word.add cseqno 1)) with (int.nat cseqno + 1) in bad by word. lia.
      }
      iMod (get_request_post with "Hargsinv Hrcptstoro HγP") as "HP"; first done.
      wp_pures.
      iNamed "Hreply".
      iApply "HΨpost".
      iFrame; iFrame "#".
      iSplitL "Herrb_ptr"; eauto.
      iSplitR ""; last by iLeft.
      iExists _; iFrame.
    }
  }
  {
    iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    simpl.
    iFrame; iFrame "#".
    iSplitL ""; eauto.
    iSplitL "Herrb_ptr"; eauto.
    replace (int.nat cseqno + 1) with (int.nat (word.add cseqno 1)) by word.
    iFrame.
    iExists {| Ret:=_; Stale:=false |}.  iFrame. by iLeft.
  }

  iIntros "LoopPost".
  wp_seq.
  iNamed "LoopPost".
  iDestruct "Hreply" as (lockReply) "[Hreply HP]". iNamed "Hreply".
  iDestruct "HP" as "[%|HP]"; first discriminate.
  wp_loadField.
  iApply "Hpost".
  iExists lockReply.(Ret); iFrame; iFrame "#".
  iSplitL ""; first done.
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
