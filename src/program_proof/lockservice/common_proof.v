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

(* Returns true iff server reported error or request "timed out" *)
Definition CallFunction (f:val) (fname:string) (rty_desc:descriptor) : val :=
  rec: fname "srv" "args" "reply" :=
    Fork (let: "dummy_reply" := struct.alloc rty_desc (zero_val (struct.t rty_desc)) in
          Skip;;
          (for: (λ: <>, #true); (λ: <>, Skip) := λ: <>,
            f "srv" "args" "dummy_reply";;
            Continue));;
    (if: nondet #()
    then f "srv" "args" "reply"
    else #true).

Lemma CallFunction_spec {A:Type} {R:Type} {a_req:@RPCRequest Σ A} (srv args reply:loc) (lockArgs:A) (lockReply:R) (f:val) (fname:string) (rty_desc:descriptor) fPre fPost γrpc γPost {r_rpc: RPCReply R rty_desc} :
has_zero (struct.t rty_desc)
-> ¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ srv' args' lockArgs' γrpc' γPost', Persistent (fPre srv' args' lockArgs' γrpc' γPost'))
-> (∀ (srv' args' reply' : loc) (lockArgs':A) 
   (lockReply' : R) (γrpc' : RPC_GS) (γPost' : gname),
{{{ fPre srv' args' lockArgs' γrpc' γPost'
    ∗ own_reply reply' lockReply'
}}}
  f #srv' #args' #reply'
{{{ RET #false; ∃ lockReply',
    own_reply reply' lockReply'
    ∗ fPost lockArgs' lockReply' γrpc'
}}}
)
      ->
{{{ "#HfPre" ∷ fPre srv args lockArgs γrpc γPost ∗ "Hreply" ∷ own_reply reply lockReply }}}
  (CallFunction f fname rty_desc) #srv #args #reply
{{{ e, RET e;
    (∃ lockReply',
    own_reply reply lockReply'
        ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ fPost lockArgs lockReply' γrpc))
}}}.
Proof.
  intros Hhas_zero Hpers Hne1 Hne2 Hne3 Hne4 Hspec.
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
    wp_apply (wp_allocStruct); first eauto.
    iIntros (l) "Hl".
    iDestruct (alloc_reply with "Hl") as "Hreply".
    wp_let. wp_pures.
    wp_apply (wp_forBreak
                (fun b => ⌜b = true⌝∗
                                   ∃ reply, (own_reply l reply)
                )%I with "[] [Hreply]");
             try eauto.

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

Definition LockServer_Function (f:val) (fname:string) (rty_desc:descriptor) (arg_desc:descriptor) : val :=
  rec: "LockServer__TryLock" "ls" "args" "reply" :=
    lock.acquire (struct.loadF LockServer.S "mu" "ls");;
    let: ("last", "ok") := MapGet (struct.loadF LockServer.S "lastSeq" "ls") (struct.loadF arg_desc "CID" "args") in
    struct.storeF rty_desc "Stale" "reply" #false;;
    (if: "ok" && (struct.loadF arg_desc "Seq" "args" ≤ "last")
    then
      (if: struct.loadF arg_desc "Seq" "args" < "last"
      then
        struct.storeF rty_desc "Stale" "reply" #true;;
        lock.release (struct.loadF LockServer.S "mu" "ls");;
        #false
      else
        struct.storeF rty_desc "OK" "reply" (Fst (MapGet (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF arg_desc "CID" "args")));;
        lock.release (struct.loadF LockServer.S "mu" "ls");;
        #false)
    else
      MapInsert (struct.loadF LockServer.S "lastSeq" "ls") (struct.loadF arg_desc "CID" "args") (struct.loadF arg_desc "Seq" "args");;
      struct.storeF rty_desc "OK" "reply" (f "ls" "args");;
      MapInsert (struct.loadF LockServer.S "lastReply" "ls") (struct.loadF arg_desc "CID" "args") (struct.loadF rty_desc "OK" "reply");;
      lock.release (struct.loadF LockServer.S "mu" "ls");;
      #false).

Context `{Ps : u64 -> iProp Σ}.
  Context `{!mapG Σ (u64*u64) (option bool)}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{!inG Σ (exclR unitO)}.
  Context `{!fmcounter_mapG Σ}.
Parameter validLocknames : gmap u64 unit.

Record TryLockArgsC :=
  mkTryLockArgsC{
  Lockname:u64;
  CID:u64;
  Seq:u64
  }.
Instance: Settable TryLockArgsC := settable! mkTryLockArgsC <Lockname; CID; Seq>.

Record TryLockReplyC :=
  mkTryLockReplyC {
  OK:bool ;
  Stale:bool
  }.
Instance: Settable TryLockReplyC := settable! mkTryLockReplyC <OK; Stale>.

Definition read_trylock_args (args_ptr:loc) (lockArgs:TryLockArgsC): iProp Σ :=
  "#HLocknameValid" ∷ ⌜is_Some (validLocknames !! lockArgs.(Lockname))⌝
  ∗ "#HSeqPositive" ∷ ⌜int.nat lockArgs.(Seq) > 0⌝
  ∗ "#HTryLockArgsOwnLockname" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "Lockname"] #lockArgs.(Lockname))
  ∗ "#HTryLockArgsOwnCID" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "CID"] #lockArgs.(CID))
  ∗ "#HTryLockArgsOwnSeq" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "Seq"] #lockArgs.(Seq))
.

Global Instance TryLockArgs_rpc : RPCRequest TryLockArgsC := { getCID x := x.(CID); getSeq x := x.(Seq) ; read_args := read_trylock_args }.

Definition own_lockreply (args_ptr:loc) (lockReply:TryLockReplyC): iProp Σ :=
  "HreplyOK" ∷ args_ptr ↦[TryLockReply.S :: "OK"] #lockReply.(OK)
  ∗ "HreplyStale" ∷ args_ptr ↦[TryLockReply.S :: "Stale"] #lockReply.(Stale)
.

#[refine] Global Instance TryLockReply_rpc : RPCReply TryLockReplyC TryLockReply.S := { own_reply := own_lockreply }.
Proof.
  { refine (λ r, r.(OK)). }
  { refine (λ r, r.(Stale)). }
  iIntros (rloc) "Halloc".
  iDestruct (struct_fields_split with "Halloc") as "(HOK&HStale&_) /=".
  iExists {| OK:=_ ; Stale:=_ |}; iFrame.
Defined.

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Definition LockServer_own_core (srv:loc) : iProp Σ :=
  ∃ (locks_ptr:loc) (locksM:gmap u64 bool),
  "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr
∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
              .

Definition LockServer_mutex_inv (srv:loc) (γrpc:RPC_GS) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool),
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ ("Hsrpc" ∷ RPCServer_own lastSeqM lastReplyM γrpc)
    ∗ LockServer_own_core srv
.

Definition replycacheinvN : namespace := nroot .@ "replyCacheInvN".
Definition mutexN : namespace := nroot .@ "lockservermutexN".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_lockserver (srv_ptr:loc) γrpc: iProp Σ :=
  ∃ mu_ptr,
      "Hmuptr" ∷ readonly (srv_ptr ↦[LockServer.S :: "mu"] #mu_ptr)
    ∗ ( "Hlinv" ∷ inv replycacheinvN (ReplyCache_inv γrpc ) )
    ∗ ( "Hmu" ∷ is_lock mutexN #mu_ptr (LockServer_mutex_inv srv_ptr γrpc))
.

Lemma LockServer_Function_spec {A:Type} {R:Type} {a_req:RPCRequest A} (srv args reply:loc) (a:A) (r:R) (f:val) (fname:string) (rty_desc:descriptor) (arg_desc:descriptor) fPre fPost {r_rpc: RPCReply R rty_desc} γrpc γPost :
has_zero (struct.t rty_desc)
-> ¬(fname = "srv") -> ¬(fname = "args") -> ¬(fname = "reply") -> ¬(fname = "dummy_reply")
-> (∀ (srv' args' : loc) (a':A),
{{{ LockServer_own_core srv'
      ∗ fPre a'
}}}
  f #srv' #args'
{{{ v, RET v; LockServer_own_core srv'
      ∗ ∃(b:bool), ⌜v = #b⌝ ∗ fPost a' b
}}}
)
->
{{{ "#Hls" ∷ is_lockserver srv γrpc 
    ∗ "#HargsInv" ∷ inv rpcRequestInvN (RPCRequest_inv fPre fPost a γrpc γPost)
    ∗ "#Hargs" ∷ read_args args a
    ∗ "Hreply" ∷ own_reply reply r
}}}
  (LockServer_Function f fname rty_desc arg_desc) #srv #args #reply
{{{ RET #false; ∃ r', own_reply reply r'
    ∗ ((⌜r'.(getStale) = true⌝ ∗ RPCRequestStale a γrpc)
  ∨ RPCReplyReceipt a r'.(getRet) γrpc)
}}}.
Proof.
Admitted.


End lockservice_common_proof.
