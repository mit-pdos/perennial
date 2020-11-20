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

Section common_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.

#[refine] Global Instance u64_pair_val : into_val.IntoVal (u64*(u64 * unit)) :=
  {
  to_val := λ x, (#x.1, (#x.2.1, #()))%V ;
  IntoVal_def := (U64(0), (U64(0), ())) ;
  IntoVal_inj := _
  }.
Proof.
  intros x1 x2 [=].
  destruct x1. destruct x2.
  simpl in *. subst. 
  destruct p.
  destruct p0.
  simpl in *.
  subst.
  by destruct u3, u1.
Defined.
(* TODO: fix this messy proof *)

Definition RPCValC:Type := u64 * (u64 * unit).

Definition read_request (args_ptr:loc) (a : @RPCRequest (RPCValC)) : iProp Σ :=
    "#HSeqPositive" ∷ ⌜int.nat a.(rpc.Seq) > 0⌝
  ∗ "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Args"] (into_val.to_val a.(Args)))
  ∗ "#HArgsOwnCID" ∷ readonly (args_ptr ↦[RPCRequest.S :: "CID"] #a.(CID))
  ∗ "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[RPCRequest.S :: "Seq"] #a.(rpc.Seq))
.

Definition own_reply (reply_ptr:loc) (r : @RPCReply (u64)) : iProp Σ :=
    "HReplyOwnStale" ∷ reply_ptr ↦[RPCReply.S :: "Stale"] #r.(Stale)
  ∗ "HReplyOwnRet" ∷ reply_ptr ↦[RPCReply.S :: "Ret"] (into_val.to_val r.(Ret))
.

Axiom nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.

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

Definition Request64 := @RPCRequest (RPCValC). (* TODO: rename these *)
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
Definition is_rpcHandler (f:val) γrpc PreCond PostCond : iProp Σ :=
  ∀ γPost req_ptr reply_ptr req reply,
    {{{ "#HargsInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req
                    ∗ "#Hargs" ∷ read_request req_ptr req
                    ∗ "Hreply" ∷ own_reply reply_ptr reply
    }}} (* TODO: put this precondition into a defn *)
      f #req_ptr #reply_ptr
    {{{ RET #false; ∃ reply',
        own_reply reply_ptr reply' ∗
        (⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale γrpc req ∨
           RPCReplyReceipt γrpc req reply'.(Ret))
    }}}
    .

Lemma is_rpcHandler_eta (e:expr) γrpc PreCond PostCond :
  □ (∀ v1 v2,
    WP subst "reply" v1 (subst "req" v2 e) {{ v, is_rpcHandler v γrpc PreCond PostCond }}) -∗
  is_rpcHandler
    (λ: "req" "reply", e (Var "req") (Var "reply"))
    γrpc PreCond PostCond.
Proof.
  iIntros "#He" (????? Φ) "!# Hpre HΦ".
  wp_pures. wp_bind (subst _ _ _).
  iApply (wp_wand with "He"). iIntros (f) "Hfhandler".
  iApply ("Hfhandler" with "Hpre"). done.
Qed.

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

(* This will alow handler functions using RPCServer__HandleRequest to establish is_rpcHandler *)
Lemma RPCServer__HandleRequest_spec (coreFunction:val) (sv:loc) γrpc server_own_core PreCond PostCond :
(∀ req : RPCRequest,
{{{ server_own_core ∗ PreCond req.(Args) }}}
  coreFunction (into_val.to_val req.(Args))%V
{{{ (r:u64), RET #r; server_own_core ∗ PostCond req.(Args) r }}}) -∗
{{{ is_rpcserver sv γrpc server_own_core }}}
  RPCServer__HandleRequest #sv coreFunction
{{{ f, RET f; is_rpcHandler f γrpc PreCond PostCond }}}.
Proof.
  iIntros "#HfCoreSpec" (Φ) "!# #Hls Hpost".
  wp_lam.
  wp_pures. iApply "Hpost". clear Φ.
  iIntros (????? Φ) "!# Hpre HΦ".
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
    iMod (server_takes_request with "[] [Hsrpc]") as "[HcorePre Hprocessing]"; eauto.
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
    iMod (server_completes_request with "[] [] HcorePost Hprocessing") as "[#Hreceipt Hsrpc] /="; eauto.
    wp_seq.
    wp_loadField.
    wp_apply (release_spec mutexN #mu_ptr _ with "[-HReplyOwnStale HReplyOwnRet HΦ]"); try iFrame "Hmu Hlocked".
    { iNext. iFrame. iExists _, _, _, _. iFrame. }
    wp_seq.
    iApply "HΦ".
    iExists {|Stale:=false; Ret:=retval |}. rewrite H1. iFrame; iFrame "#".
  }
Qed.

Lemma RemoteProcedureCall_spec (req_ptr reply_ptr:loc) (req:Request64) (reply:Reply64) (f:val) PreCond PostCond γrpc γPost :
is_rpcHandler f γrpc PreCond PostCond -∗
{{{
  "#HargsInv" ∷ is_RPCRequest γrpc γPost PreCond PostCond req ∗
  "#Hargs" ∷ read_request req_ptr req ∗
  "Hreply" ∷ own_reply reply_ptr reply
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
    wp_apply ("Hspec" with "[$Hreply]"); eauto; try iFrame "#".
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

Lemma RPCClient__MakeRequest_spec (f:val) cl_ptr args γrpc PreCond PostCond :
is_rpcHandler f γrpc PreCond PostCond -∗
{{{
  PreCond args ∗
  own_rpcclient cl_ptr γrpc ∗
  is_RPCServer γrpc
}}}
  RPCClient__MakeRequest #cl_ptr f (into_val.to_val args)
{{{ (retv:u64), RET #retv; own_rpcclient cl_ptr γrpc ∗ PostCond args retv }}}.
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
    simpl in bad. replace (int.nat (word.add cseqno 1)) with (int.nat cseqno + 1) in bad by word. lia.
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

(* TODO: need to take in γrpc as input (as opposed to allocating it ourselves) because
  the server γ has to get allocated before this is called, in order to pass it into LockServer_core_own.

  Should consider changing something to make it so this actually allocates the γrpc.
  That might be non-sensical for the crash-safe version of this.
*)
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

End common_proof.
