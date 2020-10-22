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

Lemma Clerk__TryLock_spec ck (srv:loc) (ln:u64) γrpc :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γrpc
      ∗ is_lockserver srv γrpc 
  }}}
    Clerk__TryLock ck #ln
  {{{ v, RET v; ∃(b:bool), ⌜v = #b⌝ ∗ own_clerk ck srv γrpc ∗ (⌜b = false⌝ ∨ Ps ln) }}}.
Proof using Type*.
  iIntros (Φ) "Hpre Hpost".
  iApply (Clerk__from_core _ "TryLock" with "[Hpre]"); try apply tryLock_core_spec; eauto.
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
