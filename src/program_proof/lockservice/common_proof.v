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

Definition read_request (args_ptr:loc) (a : RPCRequest) : iProp Σ :=
  let req_desc := argty_to_adesc in
    "#HSeqPositive" ∷ ⌜int.nat a.(rpc.Seq) > 0⌝
  ∗ "#HArgsOwnArgs" ∷ readonly (args_ptr ↦[req_desc :: "Args"] (into_val.to_val a.(Args)))
  ∗ "#HArgsOwnCID" ∷ readonly (args_ptr ↦[req_desc :: "CID"] #a.(CID))
  ∗ "#HArgsOwnSeq" ∷ readonly (args_ptr ↦[req_desc :: "Seq"] #a.(rpc.Seq))
.

Definition own_reply (reply_ptr:loc) (r : RPCReply) : iProp Σ :=
  let reply_desc := retty_to_rdesc in
    "HReplyOwnStale" ∷ reply_ptr ↦[reply_desc :: "Stale"] #r.(Stale)
  ∗ "#HReplyOwnRet" ∷ reply_ptr ↦[reply_desc :: "Ret"] (into_val.to_val r.(Ret))
.

End rpc_types.

Section lockservice_common_proof.

Context `{!heapG Σ}.
Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

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
Check own_reply.

Lemma CallFunction_spec {A:Type} {R:Type} {r_rpcret:RPCReturn R} {a_rpcargs:RPCArgs A} (srv req_ptr reply_ptr:loc) (req:@RPCRequest A) (reply:@RPCReply R) (f:val) (fname:string) fPre fPost γrpc γPost :
¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ srv' args' lockArgs' γrpc' γPost', Persistent (fPre srv' args' lockArgs' γrpc' γPost'))
-> (∀ (srv' req_ptr' reply_ptr' : loc) (req':RPCRequest) 
   (reply' : @RPCReply R) (γrpc' : RPC_GS) (γPost' : gname),
{{{ fPre srv' req_ptr' req' γrpc' γPost'
    ∗ @own_reply Σ _ R r_rpcret reply_ptr' reply'
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
    (∃ lockReply',
    own_reply reply lockReply' 
        ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ fPost req lockReply' γrpc))
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

Definition LockServer_Function {A:Type} {R:Type} {r_rpcret:RPCReturn R} {a_rpcargs:RPCArgs A} (f:val) (fname:string) : val :=
  rec: "LockServer__TryLock" "ls" "args" "reply" :=
    lock.acquire (struct.loadF LockServer.S "mu" "ls");;
    let: ("last", "ok") := MapGet (struct.loadF LockServer.S "lastSeq" "ls") (struct.loadF argty_to_adesc "CID" "args") in
    struct.storeF retty_to_rdesc "Stale" "reply" #false;;
    (if: "ok" && (struct.loadF argty_to_adesc "Seq" "args" ≤ "last")
    then
      (if: struct.loadF argty_to_adesc "Seq" "args" < "last"
      then
        struct.storeF retty_to_rdesc "Stale" "reply" #true;;
        lock.release (struct.loadF LockServer.S "mu" "ls");;
        #false
      else
        struct.storeF retty_to_rdesc "OK" "reply" (Fst (MapGet (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF argty_to_adesc "CID" "args")));;
        lock.release (struct.loadF LockServer.S "mu" "ls");;
        #false)
    else
      MapInsert (struct.loadF LockServer.S "lastSeq" "ls") (struct.loadF argty_to_adesc "CID" "args") (struct.loadF argty_to_adesc "Seq" "args");;
      struct.storeF retty_to_rdesc "OK" "reply" (f "ls" "args");;
      MapInsert (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF argty_to_adesc "CID" "args") (struct.loadF retty_to_rdesc "OK" "reply");;
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false).

  Context `{!mapG Σ (u64*u64) (option bool)}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{!inG Σ (exclR unitO)}.
  Context `{!fmcounter_mapG Σ}.

Definition TryLockReplyC : Type := @RPCReply bool.

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Global Instance bool_RPCReturn : RPCReturn bool.
Admitted.

Context `{Server_own_core: loc -> iProp Σ}.

Definition Server_mutex_inv (srv:loc) (γrpc:RPC_GS) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool),
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
(*
Lemma LockServer_Function_spec {A:Type} {R:Type} {a_args:RPCArgs A} {r_ret:RPCReturn R} (srv args reply:loc) (a:RPCRequest) (r:RPCReply) (f:val) (fname:string) (rty_desc:descriptor) (arg_desc:descriptor) fPre fPost γrpc γPost :
has_zero (struct.t rty_desc)
-> ¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ (srv' args' : loc) (a':A),
{{{ Server_own_core srv'
      ∗ fPre a'
}}}
  f #srv' #args'
{{{ v, RET v; Server_own_core srv'
      ∗ ∃(b:bool), ⌜v = #b⌝ ∗ fPost a' b
}}}
)
->
{{{ "#Hls" ∷ is_server srv γrpc 
    ∗ "#HreqInv" ∷ inv rpcRequestInvN (RPCRequest_inv fPre fPost a γrpc γPost)
    ∗ "#Hreq" ∷ read_request args a
    ∗ "Hreply" ∷ own_reply reply r
}}}
  (LockServer_Function f fname) #srv #args #reply
{{{ RET #false; ∃ r', own_reply reply r'
    ∗ ((⌜r'.(Stale) = true⌝ ∗ RPCRequestStale a γrpc)
  ∨ RPCReplyReceipt a r'.(Ret) γrpc)
}}}.
Proof using Type*.
  intros Hhas_zero Hne1 Hne2 Hne3 Hne4 Hpers.
  iIntros (Φ) "Hpre HPost".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  iNamed "Hls".
  wp_loadField.
  wp_apply (acquire_spec mutexN #mu_ptr _ with "Hmu").
  iIntros "(Hlocked & Hlsown)".
  iNamed "Hlsown".
  iNamed "Hreq"; iNamed "Hreply".
  wp_seq.
  repeat wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  wp_storeField.

  iAssert
    (
{{{
readonly (args ↦[argty_to_adesc :: "Seq"] #lockArgs.(Seq))
∗ ⌜int.nat lockArgs.(Seq) > 0⌝
}}}
  if: #ok then #v ≥ struct.loadF TryLockArgs.S "Seq" #args
         else #false
{{{ ifr, RET ifr; ∃b:bool, ⌜ifr = #b⌝
  ∗ ((⌜b = false⌝ ∗ ⌜int.nat v < int.nat lockArgs.(Seq)⌝)
      ∨
     (⌜b = true⌝ ∗  ⌜(int.val lockArgs.(Seq) ≤ int.val v ∧ ok=true)%Z⌝)
    )
}}}
    )%I as "Htemp".
  {
    iIntros (Ψ). iModIntro.
    iIntros "HΨpre HΨpost".
    iDestruct "HΨpre" as "[#Hseq %]".
    destruct ok.
    { wp_pures. wp_loadField. wp_binop.
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
      iMod (fmcounter_map_alloc 0 _ lockArgs.(CID) with "[$]") as "Hlseq_own_new".
      wp_pures.
      apply map_get_false in HSeqMapGet as [Hnone Hv]. rewrite Hv.
      iApply "HΨpost". iExists false.
      iSplitL ""; first done.
      iLeft. iSplitL ""; eauto.
    }
  }
  wp_apply ("Htemp" with "[]"); eauto.
  iIntros (ifr) "Hifr".
  iDestruct "Hifr" as (b ->) "Hifr".
  destruct b.
  - (* cache hit *)
    iDestruct "Hifr" as "[[% _]|[_ Hineq ]]"; first discriminate.
    iDestruct "Hineq" as %[Hineq Hok].
    rewrite ->Hok in *.
    apply map_get_true in HSeqMapGet.
    wp_pures. repeat wp_loadField. wp_binop.
    destruct bool_decide eqn:Hineqstrict.
      { (* Stale case *)
        wp_pures. wp_storeField. wp_loadField.
        apply bool_decide_eq_true in Hineqstrict.
        iMod (smaller_seqno_stale_fact with "[] Hsrpc") as "[Hsrpc #Hstale]"; eauto.
        wp_apply (release_spec mutexN #mu_ptr _ with "[-HPost HreplyOK HreplyStale]"); iFrame; iFrame "#".
        { (* Re-establish LockServer_mutex_inv *)
          iNext. iExists _, _, _, _,_,_. iFrame "#". iFrame.
        }
        wp_seq. iApply "HPost". iExists ({| OK := lockReply.(OK); Stale := true |}); iFrame.
        iLeft.
        iFrame "Hstale". by iFrame.
      }
      (* Not stale *)
      assert (v = lockArgs.(Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (int.val lockArgs.(Seq) = int.val v) by lia; word.
      }
      wp_pures.
      repeat wp_loadField.
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      iMod (server_replies_to_request with "[Hlinv] [HargsInv] [Hsrpc]") as "[#Hreceipt Hsrpc]"; eauto.
      wp_loadField.
      wp_apply (release_spec mutexN #mu_ptr _ with "[-HPost HreplyOK HreplyStale]"); iFrame; iFrame "#".
      {
        iNext. iExists _,_,_,_,_,_; iFrame "#"; iFrame.
      }
      wp_seq. iApply "HPost". iExists {| OK:=_; Stale:=_ |}; iFrame.
      iRight. simpl. iFrame "#".
    - (* cache miss *)
      iDestruct "Hifr" as "[[_ Hineq ]|[% _]]"; last discriminate.
      iDestruct "Hineq" as %Hineq.
      rename Hineq into HnegatedIneq.
      assert (int.val lockArgs.(Seq) > int.val v)%Z as Hineq; first lia.
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapInsert _ _ lastSeqM _ lockArgs.(Seq) (#lockArgs.(Seq)) with "HlastSeqMap"); try eauto.
      iIntros "HlastSeqMap".
      wp_pures.
      wp_loadField.
      wp_loadField.
      wp_apply (wp_MapGet with "HlocksMap").
      iIntros (lock_v ok2) "(HLocksMapGet&HlocksMap)"; iDestruct "HLocksMapGet" as %HLocksMapGet.
      wp_pures.
      destruct lock_v.
      + (* Lock already held by someone *)
        wp_pures.
        wp_storeField.
        repeat wp_loadField.
        wp_apply (wp_MapInsert _ _ lastReplyM _ false #false with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
        wp_seq. wp_loadField.
        iMod (server_processes_request _ _ _ _ _ false with "[Hlinv] [HargsInv] [] [Hsrpc]") as "(#Hrcptsoro & Hsrpc)"; eauto.
        { simpl. injection HSeqMapGet. intros. rewrite H0. eauto. }
        { by iLeft. }
        wp_apply (release_spec mutexN #mu_ptr _ with "[-HreplyOK HreplyStale HPost]"); try iFrame "Hmu Hlocked".
        {
          iNext. iExists _, _, _, _, _, _; iFrame; iFrame "#".
        }
        wp_seq. iApply "HPost". iExists {| OK:=_; Stale:= _|}; iFrame.
        iRight. iFrame "#".
      + (* Lock not previously held by anyone *)
        wp_pures.
        wp_storeField.
        repeat wp_loadField.
        wp_apply (wp_MapInsert with "HlocksMap"); first eauto; iIntros "HlocksMap".
        wp_seq. repeat wp_loadField.
        wp_apply (wp_MapInsert with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
        wp_seq. wp_loadField.

        iDestruct "HLocknameValid" as %HLocknameValid.
        iDestruct (big_sepM2_dom with "Hlockeds") as %HlocksDom.
        iDestruct (big_sepM2_delete _ _ _ lockArgs.(Lockname) false () with "Hlockeds") as "[HP Hlockeds]".
        {
          rewrite /map_get in HLocksMapGet.
          assert (is_Some (locksM !! lockArgs.(Lockname))) as HLocknameInLocks.
          { apply elem_of_dom. apply elem_of_dom in HLocknameValid. rewrite HlocksDom. done. }
          destruct HLocknameInLocks as [ x  HLocknameInLocks].
          rewrite HLocknameInLocks in HLocksMapGet.
            by injection HLocksMapGet as ->.
            (* TODO: Probably a better proof for this *)
        }
        { destruct HLocknameValid as [x HLocknameValid]. by destruct x. }
        iDestruct (big_sepM2_insert_delete _ _ _ lockArgs.(Lockname) true () with "[$Hlockeds]") as "Hlockeds"; eauto.
        iDestruct "HP" as "[%|HP]"; first discriminate.

        iMod (server_processes_request _ _ _ _ _ true with "Hlinv HargsInv [HP] Hsrpc") as "(#Hrcptsoro & Hlseq_own & #Hrcagree2)"; eauto.
        { simpl. apply pair_equal_spec in HSeqMapGet as [Hv _]. rewrite Hv. lia. }
        { by iRight. }
        replace (<[lockArgs.(Lockname):=()]> validLocknames) with (validLocknames).
        2:{
          rewrite insert_id; eauto. destruct HLocknameValid as [x HLocknameValid]. by destruct x.
        }

        wp_apply (release_spec mutexN #mu_ptr _ with "[-HreplyOK HreplyStale HPost]"); try iFrame "Hmu Hlocked".
        {
          iNext. iExists _, _, _, _, _, _; iFrame; iFrame "#".
        }
        wp_seq. iApply "HPost". iExists {| OK:=_; Stale:= _|}; iFrame.
        iRight. iFrame "#".
        Grab Existential Variables.
        1: done.
Admitted.
*)

End lockservice_common_proof.
