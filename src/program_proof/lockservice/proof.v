From Perennial.program_proof.lockservice Require Import lockservice fmcounter_map rpc.
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

Axiom nondet_spec:
  {{{ True }}}
    nondet #()
  {{{ v, RET v; ⌜v = #true⌝ ∨ ⌜v = #false⌝}}}.

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
Instance TryLockArgs_rpc : RPCRequest TryLockArgsC := {getCID x := x.(CID); getSeq x := x.(Seq)}.

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

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
    ∗ "Hcseq_own" ∷ (cid fm[[γrpc.(cseq)]]↦ int.nat cseqno)
.

Definition TryLock_Post : TryLockArgsC -> bool -> iProp Σ := λ args reply, (⌜reply = false⌝ ∨ (Ps args.(Lockname)))%I.
Definition TryLock_Pre : TryLockArgsC -> iProp Σ := λ _, True%I.
Definition TryLockRequest_inv := RPCRequest_inv TryLock_Pre TryLock_Post.
Check TryLockRequest_inv.

Definition LockServer_mutex_inv (srv:loc) (γrpc:RPC_GS) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr locks_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool),
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr

    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "HlocksMap" ∷ is_map (locks_ptr) locksM
    ∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
    
    ∗ ("Hlseq_own" ∷ [∗ map] cid ↦ seq ∈ lastSeqM, cid fm[[γrpc.(lseq)]]↦ int.nat seq)
    ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
.

(* Should make this readonly so it can be read by the RPC background thread *)
Definition read_lock_args (args_ptr:loc) (lockArgs:TryLockArgsC): iProp Σ :=
  "#HLocknameValid" ∷ ⌜is_Some (validLocknames !! lockArgs.(Lockname))⌝
  ∗ "#HSeqPositive" ∷ ⌜int.nat lockArgs.(Seq) > 0⌝
  ∗ "#HTryLockArgsOwnLockname" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "Lockname"] #lockArgs.(Lockname))
  ∗ "#HTryLockArgsOwnCID" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "CID"] #lockArgs.(CID))
  ∗ "#HTryLockArgsOwnSeq" ∷ readonly (args_ptr ↦[TryLockArgs.S :: "Seq"] #lockArgs.(Seq))
.

Definition own_lockreply (args_ptr:loc) (lockReply:TryLockReplyC): iProp Σ :=
  "HreplyOK" ∷ args_ptr ↦[TryLockReply.S :: "OK"] #lockReply.(OK)
  ∗ "HreplyStale" ∷ args_ptr ↦[TryLockReply.S :: "Stale"] #lockReply.(Stale)
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

Lemma TryLock_spec (srv args reply:loc) (lockArgs:TryLockArgsC) (lockReply:TryLockReplyC) γrpc γPost :
  {{{ "#Hls" ∷ is_lockserver srv γrpc 
      ∗ "#HargsInv" ∷ inv rpcRequestInvN (TryLockRequest_inv lockArgs γrpc γPost)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
LockServer__TryLock #srv #args #reply
{{{ RET #false; ∃ lockReply', own_lockreply reply lockReply'
    ∗ (⌜lockReply'.(Stale) = true⌝ ∗ (lockArgs.(CID) fm[[γrpc.(cseq)]]> ((int.nat lockArgs.(Seq)) + 1))
  ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrpc.(rc)]]↦ro (Some lockReply'.(OK)))
}}}.
Proof using Type*.
  iIntros (Φ) "Hpre HPost".
  iNamed "Hpre".
  iNamed "Hargs"; iNamed "Hreply".
  wp_lam.
  wp_pures.
  iNamed "Hls".
  wp_loadField.
  wp_apply (acquire_spec mutexN #mu_ptr _ with "Hmu").
  iIntros "(Hlocked & Hlsown)".
  iNamed "Hlsown".
  wp_seq.
  repeat wp_loadField.
  wp_apply (wp_MapGet with "HlastSeqMap").
  iIntros (v ok) "(HSeqMapGet&HlastSeqMap)"; iDestruct "HSeqMapGet" as %HSeqMapGet.
  wp_pures.
  wp_storeField.

  iAssert
    (
{{{
readonly (args ↦[TryLockArgs.S :: "Seq"] #lockArgs.(Seq))
∗ ⌜int.nat lockArgs.(Seq) > 0⌝
         ∗ ([∗ map] cid↦seq ∈ lastSeqM, cid fm[[γrpc.(lseq)]]↦int.nat seq)
}}}
  if: #ok then #v ≥ struct.loadF TryLockArgs.S "Seq" #args
         else #false
{{{ ifr, RET ifr; ∃b:bool, ⌜ifr = #b⌝
  ∗ ((⌜b = false⌝ ∗ ⌜int.nat v < int.nat lockArgs.(Seq)⌝
     ∗ ([∗ map] cid↦seq ∈ <[lockArgs.(CID):=v]> lastSeqM, cid fm[[γrpc.(lseq)]]↦int.nat seq)) ∨

     (⌜b = true⌝ ∗  ⌜(int.val lockArgs.(Seq) ≤ int.val v ∧ ok=true)%Z⌝
     ∗ ([∗ map] cid↦seq ∈ lastSeqM, cid fm[[γrpc.(lseq)]]↦int.nat seq)
     )
    )
}}}
    )%I as "Htemp".
  {
    iIntros (Ψ). iModIntro.
    iIntros "HΨpre HΨpost".
    iDestruct "HΨpre" as "[#Hseq [% Hlseq_own]]".
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
        iSplitL ""; first (iPureIntro; word).
        apply map_get_true in  HSeqMapGet.
        rewrite insert_id; eauto.
    }
    {
      iMod (fmcounter_map_alloc 0 _ lockArgs.(CID) with "[$]") as "Hlseq_own_new".
      wp_pures.
      apply map_get_false in HSeqMapGet as [Hnone Hv]. rewrite Hv.
      iApply "HΨpost". iExists false.
      iSplitL ""; first done.
      iLeft. iFrame. iSplitL ""; eauto.
      iSplitL ""; first (iPureIntro;simpl; word).
      simpl.
      Check big_sepM_insert.
      iDestruct (big_sepM_insert _ _ lockArgs.(CID) with "[$Hlseq_own Hlseq_own_new]") as "Hlseq_own"; eauto.
      by replace (int.nat 0%Z) with (0) by word.
    }
  }
  wp_apply ("Htemp" with "[$Hlseq_own]"); eauto.
  iIntros (ifr) "Hifr".
  iDestruct "Hifr" as (b ->) "Hifr".
  destruct b.
  - (* cache hit *)
    iDestruct "Hifr" as "[[% _]|[_ [Hineq Hlseq_own]]]"; first discriminate.
    iDestruct "Hineq" as %[Hineq Hok].
    rewrite ->Hok in *.
    apply map_get_true in HSeqMapGet.
    wp_pures. repeat wp_loadField. wp_binop.
    destruct bool_decide eqn:Hineqstrict.
      { (* Stale case *)
        wp_pures. wp_storeField. wp_loadField.
        wp_apply (release_spec mutexN #mu_ptr _ with "[-HPost HreplyOK HreplyStale]"); iFrame; iFrame "#".
        { (* Re-establish LockServer_mutex_inv *)
          iNext. iExists _, _, _, _,_,_. iFrame "#". iFrame.
        }
        apply bool_decide_eq_true in Hineqstrict.
        iMod (smaller_seqno_stale_fact with "[] Hrcagree") as "#Hstale"; eauto.
        wp_seq. iApply "HPost". iExists ({| OK := _; Stale := true |}); iFrame.
        iLeft.
        by iFrame "Hstale".
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
      iAssert ⌜reply_get_ok = true⌝%I as %->.
      { iDestruct (big_sepM2_lookup_1 _ _ _ lockArgs.(CID) with "Hrcagree") as "HH"; eauto.
        iDestruct "HH" as (x B) "H".
        simpl. iPureIntro. unfold map_get in HlastReplyMapGet.
        revert HlastReplyMapGet.
        rewrite B. simpl. intros. injection HlastReplyMapGet. done.
        (* TODO: get a better proof of this... *)
      }
      apply map_get_true in HlastReplyMapGet.
      iDestruct (big_sepM2_delete with "Hrcagree") as "[#Hrcptsto _]"; eauto.
      wp_loadField.
      wp_apply (release_spec mutexN #mu_ptr _ with "[-HPost HreplyOK HreplyStale]"); iFrame; iFrame "#".
      {
        iNext. iExists _,_,_,_,_,_; iFrame "#"; iFrame.
      }
      wp_seq. iApply "HPost". iExists {| OK:=_; Stale:=_ |}; iFrame.
      iRight. simpl. iFrame "#".
    - (* cache miss *)
      iDestruct "Hifr" as "[[_ [Hineq Hlseq_own]]|[% _]]"; last discriminate.
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
        iMod (server_processes_request _ _ _ _ _ false with "[Hlinv] [HargsInv] [] [Hlseq_own] [Hrcagree]") as "(#Hrcptsoro & Hlseq_own & #Hrcagree2)"; eauto.
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

        iMod (server_processes_request _ _ _ _ _ true with "Hlinv HargsInv [HP] Hlseq_own Hrcagree") as "(#Hrcptsoro & Hlseq_own & #Hrcagree2)"; eauto.
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
Qed.

Lemma CallTryLock_spec (srv args reply:loc) (lockArgs:TryLockArgsC) (lockReply:TryLockReplyC) γrpc γPost :
  {{{ "#Hls" ∷ is_lockserver srv γrpc
      ∗ "#HargsInv" ∷ inv rpcRequestInvN (TryLockRequest_inv lockArgs γrpc γPost)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
CallTryLock #srv #args #reply
{{{ e, RET e;
    (∃ lockReply', own_lockreply reply lockReply'
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ (⌜lockReply'.(Stale) = true⌝ ∗ (lockArgs.(CID) fm[[γrpc.(cseq)]]> (int.nat lockArgs.(Seq) + 1)) ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrpc.(rc)]]↦ro (Some lockReply'.(OK)))))
}}}.
Proof using Type*.
  iIntros (Φ) "Hpre Hpost".
  iNamed "Hpre".
  wp_lam.
  wp_let.
  wp_let.
  wp_apply wp_fork.
  {
    wp_apply (wp_allocStruct); first eauto.
    iIntros (l) "Hl".
    iDestruct (struct_fields_split with "Hl") as "(HOK&HStale&_)".
    iNamed "HOK".
    iNamed "HStale".
    wp_let. wp_pures.
    wp_apply (wp_forBreak
                (fun b => ⌜b = true⌝∗
                                   ∃ lockReply, (own_lockreply l lockReply)
                )%I with "[] [OK Stale]");
             try eauto.
    2: { iSplitL ""; first done. iExists {| OK:=false; Stale:=false|}. iFrame. }

    iIntros (Ψ).
    iModIntro.
    iIntros "[_ Hpre] Hpost".
    iDestruct "Hpre" as (lockReply') "Hown_reply".
    wp_apply (TryLock_spec with "[$Hown_reply]"); eauto; try iFrame "#".

    iIntros "TryLockPost".
    wp_seq.
    iApply "Hpost".
    iSplitL ""; first done.
    iDestruct "TryLockPost" as (lockReply'') "[Hown_lockreply TryLockPost]".
    iExists _. iFrame.
  }
  wp_seq.
  wp_apply (nondet_spec).
  iIntros (choice) "[Hv|Hv]"; iDestruct "Hv" as %->.
  {
    wp_pures.
    wp_apply (TryLock_spec with "[$Hreply]"); eauto; try iFrame "#".
    iDestruct 1 as (lockReply') "[Hreply TryLockPost]".
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
  iMod (alloc_γrc {| CID:=cid; Seq:=cseqno; Lockname:=ln |} _ TryLock_Pre TryLock_Post with "[Hlinv] [Hcseq_own] []") as "[Hcseq_own HallocPost]"; eauto.
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  wp_apply (wp_forBreak
              (fun b =>
 (let lockArgs := {| CID:=cid; Seq:=cseqno; Lockname:=ln |} in
    "#Hargs" ∷ read_lock_args args lockArgs
  ∗ "#Hargsinv" ∷ (inv rpcRequestInvN (TryLockRequest_inv lockArgs γrpc γP))
  ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
  ∗ "Hseq" ∷ (ck_l ↦[Clerk.S :: "seq"] #(LitInt (word.add lockArgs.(Seq) 1)))
  ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
  ∗ "Hargs_ptr" ∷ args_ptrs ↦[refT (uint64T * (uint64T * (uint64T * unitT))%ht)] #args
  ∗ "Herrb_ptr" ∷ (∃ (err:bool), errb_ptr ↦[boolT] #err)
  ∗ "Hreply" ∷ (∃ lockReply, own_lockreply reply lockReply ∗ (⌜b = true⌝ ∨ (⌜lockReply.(OK) = false⌝ ∨ Ps ln)))
  ∗ "HγP" ∷ (⌜b = false⌝ ∨ own γP (Excl ()))
  ∗ ("Hcseq_own" ∷ cid fm[[γrpc.(cseq)]]↦(int.nat lockArgs.(Seq) + 1))
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
      { iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %bad. lia. }
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
    iFrame; iFrame "#".
    iSplitL ""; first done.
    iSplitL "Herrb_ptr"; eauto.
    iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| OK:=false; Stale:=false |}. iFrame. by iLeft.
  }

  iIntros "LoopPost".
  wp_seq.
  iNamed "LoopPost".
  iDestruct "Hreply" as (lockReply) "[Hreply HP]". iNamed "Hreply".
  iDestruct "HP" as "[%|HP]"; first discriminate.
  wp_loadField.
  iApply "HΦpost".
  iExists lockReply.(OK); iFrame; iFrame "#".
  iSplitL ""; first done.
  unfold own_clerk.
  iExists _, _, (word.add cseqno 1)%nat; iFrame.
  simpl.
  iSplitL ""; first done.
  assert (int.nat cseqno + 1 = int.nat (word.add cseqno 1))%nat as <-; first by word.
  iSplit.
  { iPureIntro. lia. }
  Show Existentials.
  iFrame.
  (* TODO: where are these from? *)
  Grab Existential Variables.
  { refine true. }
  { refine true. }
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
