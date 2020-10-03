From Perennial.program_proof.lockservice Require Import lockservice.
From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From stdpp Require Import gmap.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.

Section lockservice_proof.
Context `{!heapG Σ}.

Implicit Types s : Slice.t.
Implicit Types (stk:stuckness) (E: coPset).

Axiom nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.

Record LockArgsC :=
  mkLockArgsC{
  Lockname:nat;
  CID:nat;
  Seq:nat
  }.
Instance: Settable LockArgsC := settable! mkLockArgsC <Lockname; CID; Seq>.

(*

Having token Cache(CID, S, A) should mean that 
the server has seen the seq number S, and responded with A (on a call to Lock).

{ ??? } LockServer__TryLock {RET false; ok = true → (inv (P ∨ Token)) }
The first time TryLock runs, it has P. Later on, it no longer has P, so it needs to get the invariant from somewhere.
Need to know (first time running ∨ escrow_inv_holds)

First time running iff the req.seq > lasSeq[CID]
Owning a clerk -> ck.seq > lastSeq[ck.CID]
Clerk has frag ownership of the last seq seen by the server.

∃ ls_seq ck_seq, own ls_γ ◯E(ls_seq) ∧ own ck_γ (Excl ck_seq)
(⌜ck_seq > ls_γ⌝ ∨ (resp for ck_seq is false) ∨ (inv (P ∨ Token)))

own (resp_γ ck_cid ck_seq) (Agree false)

If the first disjunct holds, then we can show that the reply cache doesn't have a response for the request.  Then, if TryLock replies true, then we have P and hence right disjunct. If TryLock replies false, we know that it will always reply false with the same input.

Use an auth_map to keep track of the reply history.

(ck_cid, ck_seq) [[rc_γ]]↦ false

Invariant for CallTryLock looks like 
∃ ls_seq ck_seq, own ls_γ ◯E(ls_seq) ∧ own ck_γ (F{1/2} ck_seq)
(⌜ck_seq > ls_γ⌝ ∨ ((ck_cid, ck_seq) [[rc_γ]]↦ false) ∨ (inv (P ∨ Token)))

Ghost state for server:
(auth_map) ck_cid [[γ]]↦ (last_seq, last_reply)

∃ ls_seq ck_seq last_reply, ∧ own ck_γ (F{1/2} ck_seq)
(⌜ck_seq > ls_γ⌝ ∨ ⌜last_reply = false⌝ ∨ (inv (P ∨ Token))) ∗
(ck_cid [[rc_γ]]↦ (ls_seq, last_reply) 
*)

  Context `{!mapG Σ nat (nat * bool)}.
  Context `{!inG Σ (exclR unitO)}.

Definition own_clerk (ck:val) (srv:val) (γ:gname) (rc_γ:gname) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid seq ls_seq :nat) (last_reply:bool),
    ⌜ck = #ck_l⌝
    ∗⌜seq > ls_seq⌝
    ∗ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ck_l ↦[Clerk.S :: "cid"] #seq
    ∗ck_l ↦[Clerk.S :: "primary"] srv
    ∗ (cid [[rc_γ]]↦ (ls_seq, last_reply))
       (*∗own γ (seq) *)
      .

Definition CallTryLock_inv (cid:nat) rc_γ P Pγ N : iProp Σ :=
  ∃ (ls_seq:nat) (seq:nat) (last_reply:bool),
    (cid [[rc_γ]]↦ (ls_seq, last_reply))
      ∗ (⌜seq > ls_seq⌝
         ∨ ⌜seq = ls_seq ∧ last_reply = false⌝
         ∨ (inv N (P ∨ own Pγ (Excl ()))))
.

(* TODO: use gmap, or gset + total map? *)
Lemma TryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) rc_γ (Ps: u64 -> (iProp Σ)) P Pγ N M:
  Ps lockArgs.(Lockname) = P →
  {{{ inv M (CallTryLock_inv lockArgs.(CID) rc_γ P Pγ N) }}}
    LockServer__TryLock #srv #args #reply
  {{{ RET #false; ∃ ok, (⌜ok = true⌝∗(inv N (P ∨ own Pγ (Excl()))) ∨ ⌜ok = false⌝) ∗ reply ↦[LockReply.S :: "OK"] #ok }}}.
Proof.
  intros HPs.
  iIntros (Φ) "HinvM HPost".
  wp_lam.
  wp_pures.
Admitted.

Lemma CallTryLock_spec (srv reply args:loc) (lockArgs:LockArgsC) (used:gset nat) rc_γ (Ps:u64 -> iProp Σ) P Pγ N M:
  lockArgs.(Lockname) ∈ used → Ps lockArgs.(Lockname) = P →
  {{{ inv M (CallTryLock_inv lockArgs.(CID) rc_γ P Pγ N) }}}
    CallTryLock #srv #args #reply
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝ ∗∃ ok, (⌜ok = false⌝ ∨ ⌜ok = true⌝∗(inv N (P ∨ own Pγ (Excl()))) ) ∗ reply ↦[LockReply.S :: "OK"] #ok }}}.
Proof.
  intros Hused Hp.
  iIntros (Φ) "#HinvM HPost".
  wp_lam.
  wp_pures.
  wp_apply wp_fork.
  { (* Background invocations of TryLock *)
    wp_bind (Alloc (_))%E.
    wp_apply wp_alloc_untyped; first by eauto.
    iIntros (l) "Hl".
    wp_pures.
    Search "wp_forBreak".
    wp_apply (wp_forBreak
                (fun b => ⌜b = true⌝%I)
             ); try eauto.
    {
      iIntros (Ψ) "_".
      iModIntro.
      iIntros "HPost".
      wp_pures.
      wp_apply (TryLock_spec); try iFrame "HinvM"; try apply Hp.
      iIntros "HTryLockPost".
      wp_seq. by iApply "HPost".
    }
  }

  wp_pures.
  wp_apply (nondet_spec).
  iIntros (choice) "[Hv|Hv]"; iDestruct "Hv" as %->.
  { (* Actually return the reply from running TryLock *)
    wp_pures. 
    wp_apply (TryLock_spec); try iFrame "HinvM"; try apply Hp.
    iIntros "HTryLockPost".
    iDestruct "HTryLockPost" as (ok) "[[[Htrue Hescrow]|Hfalse] Hrc]".
    - (* TryLock succeeded *)
      iApply "HPost". iRight.
      iSplit; try done. iExists true. iDestruct "Htrue" as %->.
      iFrame. iRight. by iFrame.
    - (* TryLock failed *)
      iApply "HPost". iRight. iSplitL ""; try done. iDestruct "Hfalse" as %->.
      iExists false. iFrame. by iLeft.
  }
  { (* Don't return any reply from TryLock *)
    wp_pures.
    iApply "HPost". by iLeft.
  }
Qed.

(*
Lemma Lock_spec ck γ (ln:u64) (Ps: gmap u64 (iProp Σ)) (P: iProp Σ) :
  Ps !! ln = Some P →
  {{{ own_clerk ck γ }}}
    Clerk__Lock ck #ln
  {{{ RET #(); own_clerk ck γ ∗ P }}}.
Proof.
Admitted.

Lemma Unlock_spec ck γ (ln:u64) (Ps: gmap u64 (iProp Σ)) (P: iProp Σ) :
  Ps !! ln = Some P →
  {{{ P ∗ own_clerk ck γ }}}
    Clerk__Unlock ck #ln
  {{{ RET #(); own_clerk ck γ }}}
.
Proof.
Admitted.
 *)

End lockservice_proof.
