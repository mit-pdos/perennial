From Perennial.program_proof.lockservice Require Import lockservice.
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
  Lockname:u64;
  CID:u64;
  Seq:u64
  }.
Instance: Settable LockArgsC := settable! mkLockArgsC <Lockname; CID; Seq>.

Record LockReplyC :=
  mkLockReplyC {
  OK:bool
  }.
Instance: Settable LockReplyC := settable! mkLockReplyC <OK>.

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

  Context `{!mapG Σ u64 (u64 * bool)}.
  Context `{!inG Σ (exclR unitO)}.

Definition own_clerk (ck:val) (srv:val) (γ:gname) (rc_γ:gname) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid seq ls_seq :u64) (last_reply:bool),
    ⌜ck = #ck_l⌝
    ∗⌜int.val seq > int.val ls_seq⌝
    ∗ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ck_l ↦[Clerk.S :: "cid"] #seq
    ∗ck_l ↦[Clerk.S :: "primary"] srv
    ∗ (cid [[rc_γ]]↦ (ls_seq, last_reply))
       (*∗own γ (seq) *)
.

Definition CallTryLock_inv (cid:u64) rc_γ (P:iProp Σ) (Pγ:gname) (N:namespace) : iProp Σ :=
  ∃ (ls_seq:u64) (seq:u64) (last_reply:bool),
    (">Hrc_ptsto" ∷ cid [[rc_γ]]↦ (ls_seq, last_reply))
      ∗ "HTryLockCases" ∷ (
         ">Hcase" ∷ ⌜int.val seq > int.val ls_seq⌝
         ∨ ">Hcase" ∷  ⌜seq = ls_seq ∧ last_reply = false⌝
         ∨ "Hcase" ∷  (inv N (P ∨ own Pγ (Excl ()))))
.

Print into_val.IntoVal.
Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Check (to_val #true).
Definition own_lockserver (srv:loc) (rc_γ:gname) (Ps: u64 -> (iProp Σ)) : iProp Σ:=
  ∃ (lastSeq_ptr lastReply_ptr locks_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool),
    (
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr
    ∗ "HlocksMap" ∷ is_map (locks_ptr) locksM
    ∗ "Hmapctx" ∷ map_ctx rc_γ 1 (map_zip lastSeqM lastReplyM)
    ∗ "HPs" ∷ [∗ map] cid ↦ held ∈ locksM, (⌜held=true⌝ ∨ (Ps cid))
    )%I
.

(* Should make this readonly so it can be read by the RPC background thread *)
Definition own_lock_args (args_ptr:loc) (lockArgs:LockArgsC): iProp Σ :=
  "#HLockArgsOwnLockname" ∷ readonly (args_ptr ↦[LockArgs.S :: "Lockname"] #lockArgs.(Lockname))
  ∗ "#HLockArgsOwnCID" ∷ readonly (args_ptr ↦[LockArgs.S :: "CID"] #lockArgs.(CID))
  ∗ "#HLockArgsOwnSeq" ∷ readonly (args_ptr ↦[LockArgs.S :: "Seq"] #lockArgs.(Seq))
.

Definition own_lock_reply (args_ptr:loc) (lockReply:LockReplyC): iProp Σ :=
  args_ptr ↦[LockReply.S :: "OK"] #lockReply.(OK)
.

Definition is_lockserver srv rc_γ Ps lockN: iProp Σ :=
  ∃ (mu_ptr:loc),
    readonly (srv ↦[LockServer.S :: "mu"] #mu_ptr)
             ∗(is_lock lockN #mu_ptr (own_lockserver srv rc_γ Ps))
.

Lemma TryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) rc_γ (Ps: u64 -> (iProp Σ)) P Pγ N M lockN:
  Ps lockArgs.(Lockname) = P →
  {{{ is_lockserver srv rc_γ Ps lockN∗inv M (CallTryLock_inv lockArgs.(CID) rc_γ P Pγ N) ∗own_lock_args args lockArgs
  ∗ own_lock_reply reply lockReply }}}
    LockServer__TryLock #srv #args #reply
  {{{ RET #false; ∃ ok, (⌜ok = true⌝∗(inv N (P ∨ own Pγ (Excl()))) ∨ ⌜ok = false⌝) ∗ reply ↦[LockReply.S :: "OK"] #ok }}}.
Proof.
  intros HPs.
  iIntros (Φ) "(#Hls & #HinvM & Hargs & Hreply) HPost".
  wp_lam.
  wp_pures.
  iDestruct "Hls" as (mu_ptr) "(Hls & Hmu)".
  wp_loadField.
  wp_apply (acquire_spec lockN #mu_ptr _ with "Hmu").
  iIntros "(Hlocked & Hlsown)".
  wp_seq.
  iNamed "Hargs".
  wp_loadField.
  iNamed "Hlsown".
  wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  destruct ok.
  - (* Case cid in lastSeqM *) admit.
  - (* Case cid not in lastSeqM, so don't look at cache *)
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_loadField.
    Check wp_MapInsert.
    wp_apply (wp_MapInsert _ _ lastSeqM _ lockArgs.(Seq) (#lockArgs.(Seq)) with "HlastSeqMap"); try eauto.
    iIntros "HlastSeqMap".
    wp_pures.
    wp_loadField.
    wp_loadField.
    wp_apply (wp_MapGet with "HlocksMap").
    iIntros (lock_v ok) "(HLocksMapGet&HlocksMap)"; iDestruct "HLocksMapGet" as %HLocksMapGet.
    wp_pures.
    destruct lock_v.
    + (* Lock already held by someone *)
      wp_pures.
      wp_storeField.
      repeat wp_loadField.
      wp_apply (wp_MapInsert _ _ lastReplyM _ false #false with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
      iApply fupd_wp.
      iInv "HinvM" as "HM" "HCloseM".
      iDestruct "HM" as (ls_seq seq last_reply) "[Hptsto #HMM]".
      iMod "Hptsto".
      iMod (map_update lockArgs.(CID) (ls_seq, last_reply) (lockArgs.(Seq), false) with "Hmapctx Hptsto") as "(Hmapctx & Hptsto)".
      rewrite (map_insert_zip_with pair _ _ lockArgs.(CID) _ _).
      iMod ("HCloseM" with "[Hptsto]") as "_".
      { iModIntro.
        unfold CallTryLock_inv.
        iExists lockArgs.(Seq).
        admit. }
      iModIntro.
      wp_seq.
      wp_loadField.
      wp_apply (release_spec lockN #mu_ptr _ with "[-Hreply HPost]"); try iFrame "Hmu Hlocked".
      { (* Estanlish own_lockserver *)
        iNext. iFrame.
        iExists _, _, _, _, _, _; iFrame.
      }
      wp_seq. iApply ("HPost").
      iExists false. iFrame. by iRight.
    + (* Lock not held by anyone *)
      wp_pures. wp_storeField. repeat wp_loadField.
      wp_apply (wp_MapInsert _ _ locksM _ true #true with "HlocksMap"); first eauto; iIntros "HlocksMap".
      wp_seq. repeat wp_loadField.
      wp_apply (wp_MapInsert _ _ lastReplyM _ true #true with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
      wp_seq.
      iDestruct (big_sepM_delete _ locksM lockArgs.(Lockname) false with "HPs") as "(HP & HPs)".
      { assert (ok=true); first admit. rewrite H in HLocksMapGet. admit. }
      iDestruct (big_sepM_insert _ (_) lockArgs.(Lockname) true with "[HPs]") as "HPs"; try iFrame.
      { admit. }
      { by iLeft. }
      rewrite (insert_delete).
      wp_loadField.
      wp_apply (release_spec lockN #mu_ptr _ with "[-Hreply HPost HP]").
      { (* Establish own_lockserver *)
        iFrame "Hmu Hlocked". iNext.
        iExists _, _, _, _, _, _; try iFrame.
        (* TODO: Update rc_γ *)
        admit.
      }
      iMod (inv_alloc N _ (P ∨ own Pγ (Excl ())) with "[HP]") as "Hescrow".
      {
        iNext. iDestruct "HP" as "[%|HP]"; first done.
        rewrite HPs. by iLeft.
      }
      wp_seq.
      iApply "HPost".
      iExists true. iFrame.
      iLeft. iSplit; try done.
Admitted.

Lemma CallTryLock_spec (srv reply args:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) (used:gset u64) rc_γ (Ps:u64 -> iProp Σ) P Pγ N M:
  lockArgs.(Lockname) ∈ used → Ps lockArgs.(Lockname) = P →
  {{{ "#HinvM" ∷ inv M (CallTryLock_inv lockArgs.(CID) rc_γ P Pγ N)
          ∗ "Hargs" ∷ own_lock_args args lockArgs
          ∗ "Hreply" ∷ own_lock_reply reply lockReply
  }}}
    CallTryLock #srv #args #reply
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝ ∗∃ ok, (⌜ok = false⌝ ∨ ⌜ok = true⌝∗(inv N (P ∨ own Pγ (Excl()))) ) ∗ reply ↦[LockReply.S :: "OK"] #ok }}}.
Proof.
  intros Hused Hp.
  iIntros (Φ).
  iNamed 1. iIntros "HPost".
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
      (*
      wp_apply (TryLock_spec with "[Hreply Hargs]"); try iFrame "HinvM Hreply Hargs".
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
*)
Admitted.

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
