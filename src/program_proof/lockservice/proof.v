From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map rpc common_proof nondet.
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
Section lockservice_proof.
Context `{!heapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Definition locknameN (lockname : u64) := nroot .@ "lock" .@ lockname.

  Context `{!mapG Σ (u64*u64) (option bool)}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{!inG Σ (exclR unitO)}.
  Context `{!fmcounter_mapG Σ}.
  Context `{Ps : u64 -> iProp Σ}.

  Parameter validLocknames : gmap u64 unit.

Definition own_clerk (ck:val) (srv:loc) (γrpc:RPC_GS) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid cseqno : u64),
    "%" ∷ ⌜ck = #ck_l⌝
    ∗ "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ "Hseq" ∷ ck_l ↦[Clerk.S :: "seq"] #cseqno
    ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
    ∗ "Hcrpc" ∷ RPCClient_own cid cseqno γrpc
.

Definition TryLock_Post : u64 -> bool -> iProp Σ := λ args reply, (⌜reply = false⌝ ∨ (Ps args))%I.
Definition TryLock_Pre : u64 -> iProp Σ := λ args, ⌜is_Some (validLocknames !! args)⌝%I.
Definition TryLockRequest_inv := RPCRequest_inv TryLock_Pre TryLock_Post.

Definition LockServer_own_core (srv:loc) : iProp Σ :=
  ∃ (locks_ptr:loc) (locksM:gmap u64 bool),
  "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr
∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
.

Definition is_lockserver := is_server (Server_own_core:=LockServer_own_core).

Definition TryLock_spec_pre (srv args reply:loc) (lockReq:@RPCRequest u64) γrpc γPost : iProp Σ
  :=
     "#Hls" ∷ is_lockserver srv γrpc
           ∗ "#HreqInv" ∷ inv rpcRequestInvN (TryLockRequest_inv lockReq γrpc γPost)
           ∗ "#Hreq" ∷ read_request args lockReq.

Lemma tryLock_core_spec (srv:loc) (tryLockArgs:u64) :
{{{ 
     LockServer_own_core srv ∗ ▷ TryLock_Pre tryLockArgs
}}}
  LockServer__tryLock_core #srv #tryLockArgs
{{{
   v, RET v; LockServer_own_core srv
      ∗ (∃b:bool, ⌜v = #b⌝ ∗ TryLock_Post tryLockArgs b)
}}}.
Proof.
Admitted.

Definition TryLockRequestC := @RPCRequest u64.
Definition TryLockReplyC := @RPCReply bool.

Lemma TryLock_spec (srv req_ptr reply_ptr:loc) (req:TryLockRequestC) (reply:TryLockReplyC) γrpc γPost :
{{{ TryLock_spec_pre srv req_ptr reply_ptr req γrpc γPost
    ∗ "Hreply" ∷ own_reply reply_ptr reply
}}}
  LockServer__TryLock #srv #req_ptr #reply_ptr
{{{ RET #false; ∃ reply', own_reply reply_ptr reply'
    ∗ ((⌜reply'.(Stale) = true⌝ ∗ RPCRequestStale req γrpc)
  ∨ RPCReplyReceipt req reply'.(Ret) γrpc)
}}}.
Proof.
  replace (LockServer__TryLock) with (LockServer_Function LockServer__tryLock_core "LockServer__TryLock"); eauto.
  iIntros (Φ) "Hpre Hpost".
  iApply (LockServer_Function_spec with "[Hpre]"); eauto.
  { apply tryLock_core_spec. } 
  iDestruct "Hpre" as "[Hpre Hreply]". iFrame.
Qed.

Lemma CallTryLock_spec (srv args reply:loc) (lockArgs:TryLockRequestC) (lockReply:TryLockReplyC) γrpc γPost :
{{{ "#Hls" ∷ is_lockserver srv γrpc
    ∗ "#HargsInv" ∷ inv rpcRequestInvN (TryLockRequest_inv lockArgs γrpc γPost)
    ∗ "#Hargs" ∷ read_request args lockArgs
    ∗ "Hreply" ∷ own_reply reply lockReply
}}}
  CallTryLock #srv #args #reply
{{{ e, RET e;
    (∃ lockReply', own_reply reply lockReply'
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝
        ∗ (⌜lockReply'.(Stale) = true⌝ ∗ RPCRequestStale lockArgs γrpc
               ∨ RPCReplyReceipt lockArgs lockReply'.(Ret) γrpc
             )))
}}}.
Proof using Type*.
  replace (CallTryLock) with (CallFunction LockServer__TryLock "CallTryLock"); eauto.
  iIntros (Φ) "Hpre Hpost".
  iApply (CallFunction_spec with "[Hpre]"); eauto; try refine TryLock_spec; eauto.
  { by rewrite /Persistent; eauto. }
  { Opaque own_reply. simpl. iNamed "Hpre". iFrame "#";iFrame. }
Qed.

Lemma Clerk__TryLock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc 
  }}}
    Clerk__TryLock ck #ln
  {{{ v, RET v; ∃(b:bool), ⌜v = #b⌝ ∗ own_clerk ck srv γrpc ∗ (⌜b = false⌝ ∨ Ps ln) }}}.
Proof using Type*.
  iIntros (Φ) "[% [Hclerk #Hsrv]] Hpost".
  iNamed "Hclerk".
  rewrite H0.
  wp_lam.
  wp_pures.
  wp_loadField.
  wp_apply (overflow_guard_incr_spec).
  iIntros (Hincr_safe).
  wp_seq.
  repeat wp_loadField.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (args) "Hargs".
  iDestruct (struct_fields_split with "Hargs") as "(HCID&HSeq&HLockname&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HLockname") as "#HLockname".
  wp_apply wp_ref_to; first eauto.
  iIntros (args_ptrs) "Hargs_ptr".
  wp_let.
  wp_loadField.
  wp_binop.
  wp_storeField.
  wp_apply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  wp_let.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (reply) "Hreply".
  wp_pures.
  iDestruct "Hsrv" as (mu_ptr) "Hsrv". iNamed "Hsrv".
  iMod (alloc_γrc {| Args:=ln; CID:=cid; rpc.Seq:=cseqno|} _ TryLock_Pre TryLock_Post with "[Hlinv] [Hcrpc] []") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  wp_apply (wp_forBreak
              (fun b =>
 (let lockArgs := ({| Args := ln; CID:= cid; rpc.Seq := cseqno|}) in
    "#Hargs" ∷ read_request args lockArgs
  ∗ "#Hargsinv" ∷ (inv rpcRequestInvN (TryLockRequest_inv lockArgs γrpc γP))
  ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
  ∗ "Hseq" ∷ (ck_l ↦[Clerk.S :: "seq"] #(LitInt (word.add lockArgs.(rpc.Seq) 1)))
  ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
  ∗ "Hargs_ptr" ∷ args_ptrs ↦[refT (uint64T * (uint64T * (uint64T * unitT))%ht)] #args
  ∗ "Herrb_ptr" ∷ (∃ (err:bool), errb_ptr ↦[boolT] #err)
  ∗ "Hreply" ∷ (∃ lockReply, own_reply reply lockReply ∗ (⌜b = true⌝ ∨ (⌜lockReply.(Ret) = false⌝ ∨ Ps ln)))
  ∗ "HγP" ∷ (⌜b = false⌝ ∨ own γP (Excl ()))
  ∗ ("Hcseq_own" ∷ cid fm[[γrpc.(cseq)]]↦(int.nat (word.add lockArgs.(rpc.Seq) 1)))
  ∗ ("HΦpost" ∷ ∀ v : val, (∃ rb : bool, ⌜v = #rb⌝ ∗ own_clerk #ck_l srv γrpc ∗ (⌜rb = false⌝ ∨ Ps ln)) -∗ Φ v)
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
    wp_apply (CallTryLock_spec with "[Hreply]"); eauto.
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
      { iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %bad. simpl in bad. replace (int.nat (word.add cseqno 1)) with (int.nat cseqno + 1) in bad by word. lia. }
      iMod (get_request_post with "Hargsinv Hrcptstoro HγP") as "HP".
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
    Transparent own_reply.
    iExists {| Ret:=false; Stale:=false |}.  iFrame. by iLeft.
  }

  iIntros "LoopPost".
  wp_seq.
  iNamed "LoopPost".
  iDestruct "Hreply" as (lockReply) "[Hreply HP]". iNamed "Hreply".
  iDestruct "HP" as "[%|HP]"; first discriminate.
  wp_loadField.
  iApply "HΦpost".
  iExists lockReply.(Ret); iFrame; iFrame "#".
  iSplitL ""; first done.
  unfold own_clerk.
  iExists _, _, (word.add cseqno 1)%nat; iFrame.
  simpl.
  iSplitL ""; first done.
  assert (int.nat cseqno + 1 = int.nat (word.add cseqno 1))%nat as <-; first by word.
  iPureIntro. lia.
Qed.

Lemma Clerk__Lock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc
  }}}
    Clerk__Lock ck #ln
  {{{ RET #true; own_clerk ck srv γrpc ∗ Ps ln }}}.
Proof using Type*.
  iIntros (Φ) "[% [Hclerk_own #Hinv]] Hpost".
  wp_lam.
  wp_pures.
  wp_apply (wp_forBreak
              (fun c =>
                 (own_clerk ck srv γrpc ∗ Ps ln -∗ Φ #true)
                 ∗ own_clerk ck srv γrpc
                 ∗ (⌜c = true⌝ ∨ ⌜c = false⌝∗ Ps ln)
              )%I
           with "[] [$Hclerk_own $Hpost]"); eauto.
  {
    iIntros (Ψ).
    iModIntro. iIntros "[HΦpost [Hclerk_own _]] Hpost".
    wp_apply (Clerk__TryLock_spec with "[$Hclerk_own]"); eauto.
    iIntros (tl_r) "TryLockPost".
    iDestruct "TryLockPost" as (acquired ->) "[Hown_clerk TryLockPost]".
    destruct acquired.
    {
      wp_pures.
      iApply "Hpost".
      iFrame. iRight.
      iDestruct "TryLockPost" as "[% | HP]"; first discriminate.
      eauto.
    }
    {
      wp_pures.
      iApply "Hpost".
      iFrame. by iLeft.
    }
  }
  iIntros "(Hpost & Hown_clerk & [% | (_ & HP)])"; first discriminate.
  wp_seq.
  iApply "Hpost".
  iFrame.
Qed.

End lockservice_proof.
