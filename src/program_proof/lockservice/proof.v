From Perennial.program_proof.lockservice Require Import lockservice.
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
From iris.algebra Require Import numbers.
From Coq.Structures Require Import OrdersTac.
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

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Definition locknameN (lockname : u64) := nroot .@ "lock" .@ lockname.

  Context `{!mapG Σ u64 (u64 * bool)}.
  Context `{!mapG Σ u64 u64}.
  Context `{!mapG Σ (u64*u64) (option bool)}.
  Context `{!inG Σ (exclR unitO)}.
  Context `{!inG Σ (gmapUR u64 fmcounterUR)}.
  Context `{!inG Σ (gmapUR u64 (lebnizO boolO))}.

Definition own_clerk (ck:val) (srv:val) (γ:gname) (rcγ:gname) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid seq ls_seq : u64) (last_reply:bool),
    ⌜ck = #ck_l⌝
    ∗⌜int.val seq > int.val ls_seq⌝%Z
    ∗ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ck_l ↦[Clerk.S :: "cid"] #seq
    ∗ck_l ↦[Clerk.S :: "primary"] srv
    ∗ (cid [[rcγ]]↦ (ls_seq, last_reply))
       (*∗own γ (seq) *)
.

(* Either the request owns the lastSeq[cid] ptsto, or it
knows that it won't need it by way of knowing that lastSeq[cid] >= seq *)
Definition LockReq_inner (seq cid ln:u64) rcγ lseqγ req_owns_lseqγ (Ps:u64 -> iProp Σ) (Pγ:gname) : iProp Σ :=
  "Hlseq_prop" ∷ ( (∃ lseq : u64,
        ⌜int.nat lseq ≤ int.nat seq⌝ ∗
         own lseqγ {[ cid := (●{1/2}MaxNat (int.nat lseq))]} 
         ∗ (⌜int.nat lseq < int.nat seq⌝ ∨ (∃ (last_reply:bool), (cid, seq) [[rcγ]]↦ro Some last_reply
                          ∗ ⌜lseq = seq⌝ ∗ (⌜last_reply = false⌝ ∨ (Ps ln) ∨ own Pγ (Excl ())))
                   ))
                   ∨
                   (own req_owns_lseqγ (Excl ())) ∗ (own lseqγ {[ cid := (◯MaxNat (int.nat seq)) ]} )
                 )
(*
  ∗
  "Hrc_ptsto" ∷ (
  (cid, seq) [[rcγ]]↦ None
  ∨ (∃ (last_reply:bool), (cid, seq) [[rcγ]]↦ro Some last_reply
  ∗ (own lseqγ {[ cid := (◯MaxNat (int.nat seq)) ]} ) ∗ (⌜last_reply = false⌝ ∨ (Ps ln) ∨ own Pγ (Excl ())))
  )
 *)
.

Definition own_lockserver (srv:loc) (rcγ:gname) (lseqγ:gname) (Ps: u64 -> (iProp Σ)) : iProp Σ:=
  ∃ (lastSeq_ptr lastReply_ptr locks_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool) (replyHistory:gmap (u64*u64) (option bool)),
    (
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr

    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "HlocksMap" ∷ is_map (locks_ptr) locksM

    ∗ ("Hrcctx" ∷ map_ctx rcγ 1 replyHistory)
    ∗ ("Hownlseqγ" ∷ [∗ map] cid ↦ lseq ∈ lastSeqM, own lseqγ {[ cid := (●{1/2}MaxNat (int.nat lseq))]} )
    ∗ ("#Hrc_lseqbound" ∷ [∗ map] cid_seq ↦ r ∈ replyHistory, own lseqγ {[ cid_seq.1 := (◯MaxNat (int.nat cid_seq.2))]} )

    ∗ ("#Htbd" ∷ [∗ map] cid_seq ↦ r ∈ replyHistory,
       ⌜r = None⌝ ∨ cid_seq [[rcγ]]↦ro r)

    ∗ ("%" ∷ ⌜forall (cid seq:u64) r, lastSeqM !! cid = Some seq ∧ lastReplyM !! cid = Some r → replyHistory !! (cid, seq) = Some (Some r)⌝)
    ∗ ("%" ∷ ⌜forall (cid seq:u64), lastSeqM !! cid = Some seq → (∃ r, lastReplyM !! cid = Some r)⌝)

    ∗ "Hlockeds" ∷ [∗ map] ln ↦ locked ∈ locksM, (⌜locked=true⌝ ∨ (Ps ln))
    )%I
.

(* Should make this readonly so it can be read by the RPC background thread *)
Definition read_lock_args (args_ptr:loc) (lockArgs:LockArgsC): iProp Σ :=
  "#HLockArgsOwnLockname" ∷ readonly (args_ptr ↦[LockArgs.S :: "Lockname"] #lockArgs.(Lockname))
  ∗ "#HLockArgsOwnCID" ∷ readonly (args_ptr ↦[LockArgs.S :: "CID"] #lockArgs.(CID))
  ∗ "#HLockArgsOwnSeq" ∷ readonly (args_ptr ↦[LockArgs.S :: "Seq"] #lockArgs.(Seq))
.

Definition own_lock_reply (args_ptr:loc) (lockReply:LockReplyC): iProp Σ :=
  args_ptr ↦[LockReply.S :: "OK"] #lockReply.(OK)
.

Definition is_lockserver srv rcγ lseqγ Ps lockN: iProp Σ :=
  ∃ (mu_ptr:loc),
    "Hmuptr" ∷ readonly (srv ↦[LockServer.S :: "mu"] #mu_ptr)
             ∗ ( "Hmu" ∷ is_lock lockN #mu_ptr (own_lockserver srv rcγ lseqγ Ps))
.

Instance inj_MaxNat_equiv : Inj eq equiv MaxNat.
Proof.
  intros n1 n2.
  intros ?%leibniz_equiv.
  inversion H0; auto.
Qed.

Lemma TryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) rcγ (lseqγ:gname) req_owns_lseqγ (Ps: u64 -> (iProp Σ)) P Pγ M lockN :
  Ps lockArgs.(Lockname) = P →
  {{{ "#Hls" ∷ is_lockserver srv rcγ lseqγ Ps lockN
      ∗ "#HargsInv" ∷ inv M (LockReq_inner lockArgs.(Seq) lockArgs.(CID) lockArgs.(Lockname) rcγ lseqγ req_owns_lseqγ Ps Pγ)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lock_reply reply lockReply
      ∗ "Hcond_own" ∷ own req_owns_lseqγ (Excl ())
  }}}
LockServer__TryLock #srv #args #reply
{{{ RET #false; ∃ (ok:bool), reply ↦[LockReply.S :: "OK"] #ok
                                   ∗ (lockArgs.(CID), lockArgs.(Seq)) [[rcγ]]↦ro (Some ok)
}}}.
Proof.
  intros HPs.
  iIntros (Φ) "Hpre HPost".
  iNamed "Hpre".
  wp_lam.
  wp_pures.
  iNamed "Hls".
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
  - (* Case cid in lastSeqM *)
    apply map_get_true in HSeqMapGet.
    wp_pures. repeat wp_loadField. wp_binop.
    destruct bool_decide eqn:Hineq.
    -- (* old seqno *)
      apply bool_decide_eq_true in Hineq.
      wp_pures. 
      repeat wp_loadField.
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      assert (reply_get_ok = true) as ->; first admit.
      apply map_get_true in HlastReplyMapGet.
      iApply fupd_wp.

      (* Use invariant to get Hrc_ptsto, and know that its seqno matches the seqno in request *)
      iInv M as "HMinner" "HMClose".
      iDestruct "HMinner" as "Hlseq_prop".
      iDestruct "Hlseq_prop" as "[Hlseq_prop|Hlseq_bad]"; last admit.
      iDestruct "Hlseq_prop" as (real_lseq) "[#>Hle [>Hlseq_own Hcases]]".
      iDestruct "Hle" as %Hle.
      iDestruct (big_sepM_delete _ _ lockArgs.(CID) v with "Hownlseqγ") as "(Hlseq_frombigSep & Hlseqγauth)"; first done.
      iCombine "Hlseq_own Hlseq_frombigSep" as "Hcombined".
      iDestruct (own_valid with "Hcombined") as %Hvalid.
      apply singleton_valid in Hvalid.
      apply auth_auth_frac_op_inv in Hvalid.
      symmetry in Hvalid.
      apply (inj MaxNat) in Hvalid.
      assert (v = real_lseq) as Htemp. {
        replace (v) with (real_lseq) by word. done.
      }
      destruct Htemp.
      destruct Hvalid.
      iDestruct "Hcombined" as "[Hlseq_own Hlseq_frombigSep]".
      iDestruct (big_sepM_delete _ _ lockArgs.(CID) v with "[$Hlseqγauth $Hlseq_frombigSep]") as "Hlseqγauth"; first done.
      
      assert (v = lockArgs.(Seq)) as ->; first admit. (* By inequalities *)
      iDestruct (big_sepM_delete _ _ (lockArgs.(CID), lockArgs.(Seq)) (Some reply_v) with "Htbd") as "(#Hreply_prop & _)".
      {
        (* Using foralls *)
        admit.
      }
      iMod ("HMClose" with "[Hlseq_own Hcases]") as "_".
      { iNext. iLeft. iExists _; iFrame. iFrame "%". }
      iModIntro.

      iDestruct "Hreply_prop" as "[Hbad|Hrc_ptsto]".
      { iDestruct "Hbad" as %Hbad; iExFalso; iPureIntro. discriminate Hbad. }
      wp_loadField.
      wp_apply (release_spec lockN #mu_ptr _ with "[-Hreply Hcond_own Hrc_ptsto HPost]"); try iFrame "Hmu Hlocked".
      {
        iNext. iExists _, _, _, _, _, _, _; try iFrame; try iFrame "#"; try iFrame "%".
      }

      wp_seq.
      iApply "HPost".
      iExists reply_v.
      iFrame "#"; iFrame.
    -- (* new seqno *)
      apply bool_decide_eq_false in Hineq.
      rename Hineq into HnegatedIneq.
      assert (int.val lockArgs.(Seq) > int.val v)%Z as Hineq; first lia.
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
        wp_seq. wp_loadField.
        iApply fupd_wp.
        iInv M as "HMinner" "HMClose".
        iDestruct "HMinner" as "[HMinner|Hbad]"; last admit.
        iDestruct "HMinner" as (real_lseq) "[#>Hle [>Hlseq_own Hcases]]".
        assert (v = real_lseq) as Htemp; first admit. (* TODO: make this a lemma *)
        Check map_alloc.
        iAssert ⌜replyHistory !! (lockArgs.(CID), lockArgs.(Seq)) = None⌝%I as %HtempMap.
        {
          admit.
        }
        iMod (map_alloc_ro (lockArgs.(CID), lockArgs.(Seq)) (Some false) with "Hrcctx") as "[Hrcctx #Hrc_ptsto]"; first done.
        iDestruct (big_sepM_delete _ _ lockArgs.(CID) v with "Hownlseqγ") as "(Hlseq_frombigSep & Hlseqγauth)"; first done.
        Check own_update_2.
        destruct Htemp.
        iCombine "Hlseq_frombigSep Hlseq_own" as "Hcombined".
        iMod (own_update with "Hcombined") as "Hcombined".
        {
          eapply singleton_update.
          eapply auth_update_alloc.
          eapply (max_nat_local_update _ _ (MaxNat (int.nat lockArgs.(Seq)))). simpl. lia.
        }
        iDestruct "Hcombined" as "[[Hlseq_frombigSep Hlseq_own] Hfrag]".
        iDestruct (big_sepM_insert_delete with "[$Hlseqγauth $Hlseq_frombigSep]") as "Hlseqγauth".
        Check big_sepM_insert.
        iDestruct (big_sepM_insert _ _ (lockArgs.(CID), lockArgs.(Seq)) _ with "[$Hrc_lseqbound $Hfrag]") as "#Hrc_lseqbound2"; first done.
        iDestruct (big_sepM_insert _ _ (lockArgs.(CID), lockArgs.(Seq)) _ with "[$Htbd $Hrc_ptsto]") as "#Htbd2"; first done.
        
        iMod ("HMClose" with "[Hrc_ptsto Hcases Hlseq_own]") as "_".
        { iNext. iLeft. iExists _; iFrame. iFrame "#".
          iSplitL ""; first done. iRight. iExists false. iFrame "#".
          iSplitL ""; first done. by iLeft.
        }
        iModIntro.
        wp_apply (release_spec lockN #mu_ptr _ with "[-Hreply HPost]"); try iFrame "Hmu Hlocked".
        { (* Re-establish own_lockserver *)
          iNext. iExists _, _, _, _, _, _, _; try iFrame; try iFrame "#"; try iFrame "%".
          iPureIntro.
          split.
          {
            intros.
            admit.
          }
          {
            intros.
            admit.
          }
        }
        wp_seq.
        iApply "HPost".
        iExists false. iFrame. iFrame "#".
      + (* Lock not held by anyone *)

(*
        iApply fupd_wp.
        iInv M as "HMinner" "HCloseM".
        iDestruct "HMinner" as (lseq_fi _) "HMinner".
        iMod (map_update lockArgs.(CID) (lseq_fi, last_reply) (lockArgs.(Seq), false) with "Hmapctx Hptsto") as "(Hmapctx & Hptsto)".
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
          ∗ "Hargs" ∷ read_lock_args args lockArgs
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
*)*)
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
