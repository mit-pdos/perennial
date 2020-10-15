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
  OK:bool ;
  Stale:bool
  }.
Instance: Settable LockReplyC := settable! mkLockReplyC <OK; Stale>.

Global Instance ToVal_bool : into_val.IntoVal bool.
Proof.
  refine {| into_val.to_val := λ (x: bool), #x;
            IntoVal_def := false; |}; congruence.
Defined.

Definition locknameN (lockname : u64) := nroot .@ "lock" .@ lockname.

  Context `{!mapG Σ (u64*u64) (option bool)}.
  Context `{!mapG Σ (u64*u64) unit}.
  Context `{!inG Σ (exclR unitO)}.
  Context `{!inG Σ (gmapUR u64 fmcounterUR)}.

  Parameter validLocknames : gmap u64 unit.

Definition fmcounter_map_own γ (k:u64) q n := own γ {[ k := (●{q}MaxNat n)]}.
Definition fmcounter_map_lb γ (k:u64) n := own γ {[ k := (◯MaxNat n)]}.

Notation "k fm[[ γ ]]↦{ q } n " := (fmcounter_map_own γ k q%Qp n)
(at level 20, format "k fm[[ γ ]]↦{ q }  n") : bi_scope.
Notation "k fm[[ γ ]]↦ n " := (k fm[[ γ ]]↦{ 1 } n)%I
(at level 20, format "k fm[[ γ ]]↦ n") : bi_scope.
Notation "k fm[[ γ ]]≥ n " := (fmcounter_map_lb γ k n)
(at level 20, format "k fm[[ γ ]]≥ n") : bi_scope.
Notation "k fm[[ γ ]]> n " := (fmcounter_map_lb γ k (n + 1))
(at level 20, format "k fm[[ γ ]]> n") : bi_scope.

Lemma fmcounter_map_get_lb γ k q n :
      k fm[[γ]]↦{q} n ==∗ k fm[[γ]]↦{q} n ∗ k fm[[γ]]≥ n.
Admitted.

Lemma fmcounter_map_update γ k n n':
  n ≤ n' ->
      k fm[[γ]]↦ n ==∗ k fm[[γ]]↦ n'.
Admitted.

Lemma fmcounter_map_agree_lb γ k q n1 n2 :
  k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]≥ n2 -∗ ⌜n1 ≥ n2⌝.
Admitted.

Lemma fmcounter_map_agree_strict_lb γ k q n1 n2 :
  k fm[[γ]]↦{q} n1 -∗ k fm[[γ]]> n2 -∗ ⌜n1 > n2⌝.
Admitted.


(* TODO: out of date, needs to be re-written *)
Definition own_clerk (ck:val) (srv:loc) (γcseq:gname) : iProp Σ
  :=
  ∃ (ck_l:loc) (cid seq : u64) (last_reply:bool),
    "%" ∷ ⌜ck = #ck_l⌝
    ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
    ∗ "Hseq" ∷ ck_l ↦[Clerk.S :: "seq"] #seq
    ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
    ∗ "Hcseq_own" ∷ (cid fm[[γcseq]]↦ int.nat seq)
.

Definition LockRequest_inv (lockArgs:LockArgsC) γrc γlseq γcseq (Ps:u64 -> iProp Σ) (γP:gname) : iProp Σ :=
   "#Hlseq_bound" ∷ lockArgs.(CID) fm[[γcseq]]> int.nat lockArgs.(Seq)
  ∗ ("Hreply" ∷ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ None ∨
      lockArgs.(CID) fm[[γlseq]]≥ int.nat lockArgs.(Seq)
      ∗ (∃ (last_reply:bool), (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro Some last_reply
        ∗ (⌜last_reply = false⌝ ∨ (Ps lockArgs.(Lockname)) ∨ own γP (Excl ()))
      )
    )
.

Definition ReplyCache_inv (γrc γcseq:gname) (Ps: u64 -> (iProp Σ)) : iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option bool),
      ("Hrcctx" ∷ map_ctx γrc 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γcseq]]> int.nat cid_seq.2)
.

Definition LockServer_mutex_inv (srv:loc) (γrc γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) : iProp Σ :=
  ∃ (lastSeq_ptr lastReply_ptr locks_ptr:loc) (lastSeqM:gmap u64 u64)
    (lastReplyM locksM:gmap u64 bool),
      "HlastSeqOwn" ∷ srv ↦[LockServer.S :: "lastSeq"] #lastSeq_ptr
    ∗ "HlastReplyOwn" ∷ srv ↦[LockServer.S :: "lastReply"] #lastReply_ptr
    ∗ "HlocksOwn" ∷ srv ↦[LockServer.S :: "locks"] #locks_ptr

    ∗ "HlastSeqMap" ∷ is_map (lastSeq_ptr) lastSeqM
    ∗ "HlastReplyMap" ∷ is_map (lastReply_ptr) lastReplyM
    ∗ "HlocksMap" ∷ is_map (locks_ptr) locksM
    
    ∗ ("Hlseq_own" ∷ [∗ map] cid ↦ seq ∈ lastSeqM, cid fm[[γlseq]]↦ int.nat seq)
    ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrc]]↦ro Some r)
    ∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
.

(* Should make this readonly so it can be read by the RPC background thread *)
Definition read_lock_args (args_ptr:loc) (lockArgs:LockArgsC): iProp Σ :=
  "#HLockArgsOwnLockname" ∷ readonly (args_ptr ↦[LockArgs.S :: "Lockname"] #lockArgs.(Lockname))
  ∗ "#HLocknameValid" ∷ ⌜is_Some (validLocknames !! lockArgs.(Lockname))⌝
  ∗ "#HLockArgsOwnCID" ∷ readonly (args_ptr ↦[LockArgs.S :: "CID"] #lockArgs.(CID))
  ∗ "#HLockArgsOwnSeq" ∷ readonly (args_ptr ↦[LockArgs.S :: "Seq"] #lockArgs.(Seq))
.

Definition own_lockreply (args_ptr:loc) (lockReply:LockReplyC): iProp Σ :=
  "HreplyOK" ∷ args_ptr ↦[LockReply.S :: "OK"] #lockReply.(OK)
  ∗ "HreplyStale" ∷ args_ptr ↦[LockReply.S :: "Stale"] #lockReply.(Stale)
.

Definition replycacheinvN : namespace := nroot .@ "replycacheinvN".
Definition mutexN : namespace := nroot .@ "lockservermutex".
Definition lockRequestInvN (cid seq : u64) := nroot .@ "lock" .@ cid .@ "," .@ seq.

Definition is_lockserver (srv_ptr:loc) γrc γlseq γcseq Ps: iProp Σ :=
  ∃ mu_ptr,
      "Hmuptr" ∷ readonly (srv_ptr ↦[LockServer.S :: "mu"] #mu_ptr)
    ∗ ( "Hlinv" ∷ inv replycacheinvN (ReplyCache_inv γrc γcseq Ps ) )
    ∗ ( "Hmu" ∷ is_lock mutexN #mu_ptr (LockServer_mutex_inv srv_ptr γrc γlseq γcseq Ps))
.

Lemma TryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) (γrc γi γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) γP M :
  {{{ "#Hls" ∷ is_lockserver srv γrc γlseq γcseq Ps
      ∗ "#HargsInv" ∷ inv M (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
LockServer__TryLock #srv #args #reply
{{{ RET #false; ∃ lockReply', own_lockreply reply lockReply'
            ∗ (⌜lockReply'.(Stale) = true⌝ ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro (Some lockReply'.(OK)))
}}}.
Proof.
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
  destruct ok.
  - (* Case cid in lastSeqM *)
    apply map_get_true in HSeqMapGet.
    wp_storeField.
    wp_pures. repeat wp_loadField. wp_binop.
    destruct bool_decide eqn:Hineq.
    -- (* old seqno *)
      apply bool_decide_eq_true in Hineq.
      wp_pures. 
      wp_loadField. wp_binop.
      destruct bool_decide eqn:Hineqstrict.
      { (* Stale case *)
        wp_pures. wp_storeField. wp_loadField.
        wp_apply (release_spec mutexN #mu_ptr _ with "[-HPost HreplyOK HreplyStale]"); iFrame; iFrame "#".
        { (* Re-establish LockServer_mutex_inv *)
          iNext. iExists _, _, _, _,_,_. iFrame "#". iFrame.
        }
        wp_seq. iApply "HPost". iExists ({| OK := _; Stale := true |}); iFrame.
        iLeft. done.
      }
      (* Not stale *)
      assert (v = lockArgs.(Seq)) as ->. {
        (* not strict + non-strict ineq ==> eq *)
        apply bool_decide_eq_false in Hineqstrict.
        assert (int.val lockArgs.(Seq) = int.val v) by lia.
        by word.
      }
      wp_pures.
      repeat wp_loadField.
      wp_apply (wp_MapGet with "HlastReplyMap").
      iIntros (reply_v reply_get_ok) "(HlastReplyMapGet & HlastReplyMap)"; iDestruct "HlastReplyMapGet" as %HlastReplyMapGet.
      wp_storeField.
      iAssert ⌜reply_get_ok = true⌝%I as %->.
      { iDestruct (big_sepM2_lookup_1 _ _ _ lockArgs.(CID) with "Hrcagree") as "HH"; first done.
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
    -- (* new seqno *)
      apply bool_decide_eq_false in Hineq.
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
        iInv M as "[#>Hargseq_lb Hcases]" "HMClose".
        iDestruct "Hcases" as "[>Hunproc|Hproc]".
        {
          iInv replycacheinvN as ">HNinner" "HNClose"; first admit.
          (* Give unique namespaces to invariants *)
          iNamed "HNinner".
          iDestruct (map_update _ _ (Some false) with "Hrcctx Hunproc") as ">[Hrcctx Hrcptsto]".
          iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
          iDestruct (big_sepM_insert_2 _ _ (lockArgs.(CID), lockArgs.(Seq)) (Some false) with "[Hargseq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
          iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
          { iNext. iExists _; iFrame; iFrame "#". }

          iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first done.
          iMod (fmcounter_map_update _ _ _ (int.nat lockArgs.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
          iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
          iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
          iMod ("HMClose" with "[]") as "_".
          { iNext. iFrame "#". iRight. iFrame. iExists _; iFrame "#". by iLeft. }
          iModIntro.

          iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM lockArgs.(CID) lockArgs.(Seq) false with "[Hargseq_lb] Hrcagree") as "Hrcagree2"; eauto.
          wp_apply (release_spec mutexN #mu_ptr _ with "[-HreplyOK HreplyStale HPost]"); try iFrame "Hmu Hlocked".
          {
            iNext. iExists _, _, _, _, _, _; iFrame; iFrame "#".
          }
          wp_seq. iApply "HPost". iExists {| OK:=_; Stale:= _|}; iFrame.
          iRight. iFrame "#".
        }
        { (* One-shot update of γrc already happened; this is impossible *)
          iDestruct "Hproc" as "[#>Hlseq_lb _]".
          iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first done.
          iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
          iExFalso; iPureIntro. (* TODO: Have contradictory hypotheses Hlseq_lb_ineq and Hineq *)
          admit.
        }
      + wp_pures.
        wp_storeField.
        repeat wp_loadField.
        wp_apply (wp_MapInsert with "HlocksMap"); first eauto; iIntros "HlocksMap".
        wp_seq. repeat wp_loadField.
        wp_apply (wp_MapInsert with "HlastReplyMap"); first eauto; iIntros "HlastReplyMap".
        wp_seq. wp_loadField.
        iApply fupd_wp.
        iInv M as "[#>Hargseq_lb Hcases]" "HMClose".
        iDestruct "Hcases" as "[>Hunproc|Hproc]".
        {
          iInv replycacheinvN as ">HNinner" "HNClose"; first admit.
          (* Give unique namespaces to invariants *)
          iNamed "HNinner".
          iDestruct (map_update _ _ (Some true) with "Hrcctx Hunproc") as ">[Hrcctx Hrcptsto]".
          iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
          iDestruct (big_sepM_insert_2 _ _ (lockArgs.(CID), lockArgs.(Seq)) (Some true) with "[Hargseq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
          iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
          { iNext. iExists _; iFrame; iFrame "#". }

          iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first done.
          iMod (fmcounter_map_update _ _ _ (int.nat lockArgs.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
          iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
          iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
          iDestruct "HLocknameValid" as %HLocknameValid.
          iDestruct (big_sepM2_dom with "Hlockeds") as %HlocksDom.
          iDestruct (big_sepM2_delete _ _ _ lockArgs.(Lockname) false with "Hlockeds") as "[HP Hlockeds]".
          {
            rewrite /map_get in HLocksMapGet.
            assert (is_Some (locksM !! lockArgs.(Lockname))) as HLocknameInLocks.
            { apply elem_of_dom. apply elem_of_dom in HLocknameValid. rewrite HlocksDom. done. }
            destruct HLocknameInLocks as [ x  HLocknameInLocks].
            rewrite HLocknameInLocks in HLocksMapGet.
            by injection HLocksMapGet as ->.
            (* TODO: Probably a better proof for this *)
          }
          { admit. }
          iDestruct "HP" as "[% | HP]"; first discriminate.
          iMod ("HMClose" with "[HP]") as "_".
          { iNext. iFrame "#". iRight. iFrame. iExists _; iFrame "#". }
          iModIntro.

          iDestruct (big_sepM2_insert_delete _ _ _ lockArgs.(Lockname) true () with "[$Hlockeds]") as "Hlockeds"; eauto.
          iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM lockArgs.(CID) lockArgs.(Seq) true with "[Hargseq_lb] Hrcagree") as "Hrcagree2"; eauto.
          wp_apply (release_spec mutexN #mu_ptr _ with "[-HreplyOK HreplyStale HPost]"); try iFrame "Hmu Hlocked".
          {
            iNext. iExists _, _, _, _, _, _; iFrame; iFrame "#".
            (* Related to validLocknames *)
            admit. 
          }
          wp_seq. iApply "HPost". iExists {| OK:=_; Stale:= _|}; iFrame.
          iRight. iFrame "#".
        }
        { (* One-shot update of γrc already happened; this is impossible *)
          iDestruct "Hproc" as "[#>Hlseq_lb _]".
          iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first done.
          iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
          iExFalso; iPureIntro. (* TODO: Have contradictory hypotheses Hlseq_lb_ineq and Hineq *)
          admit.
        }
  - (* Case when CID not in lastSeq *)
    admit.
Admitted.

Lemma CallTryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) (γrc γi γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) γP M:
  {{{ "#Hls" ∷ is_lockserver srv γrc γlseq γcseq Ps
      ∗ "#HargsInv" ∷ inv M (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
CallTryLock #srv #args #reply
{{{ e, RET e;
    (∃ lockReply', own_lockreply reply lockReply'
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ (⌜lockReply'.(Stale) = true⌝ ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro (Some lockReply'.(OK)))))
}}}.
Proof.
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


Lemma alloc_γrc (cid seq ln:u64) γrc γlseq γcseq Ps:
  inv replycacheinvN (ReplyCache_inv γrc γcseq Ps)
      ∗ cid fm[[γcseq]]↦ int.nat seq
  ={⊤}=∗
      cid fm[[γcseq]]↦ (int.nat seq + 1)
      ∗ (∃ γP, inv (lockRequestInvN cid seq) (LockRequest_inv {| CID:=cid; Seq:=seq; Lockname:= ln |} γrc γlseq γcseq Ps γP)).
Proof using mapG1.
  (* TODO: Why is the above necessary? *)
  intros.
  iIntros "[Hinv Hcseq_own]".
  iInv replycacheinvN as ">Hrcinv" "HNclose".
  iNamed "Hrcinv".
  destruct (replyHistory !! (cid, seq)) eqn:Hrh.
  {
    iExFalso.
    iDestruct (big_sepM_delete _ _ (cid, seq) with "Hcseq_lb") as "[Hbad _]"; first eauto.
    simpl.
    iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %Hbad.
    iPureIntro. simpl in Hbad.
    lia.
  }
  iMod (map_alloc (cid, seq) None with "Hrcctx") as "[Hrcctx Hrcptsto]"; first done.
  iMod (own_alloc (Excl ())) as "HγP"; first done.
  iDestruct "HγP" as (γP) "HγP".
  iMod (fmcounter_map_update γcseq cid _ (int.nat seq + 1) with "Hcseq_own") as "Hcseq_own".
  { simpl. lia. }
  iMod (fmcounter_map_get_lb with "Hcseq_own") as "[Hcseq_own #Hcseq_lb_one]".
  iDestruct (big_sepM_insert _ _ (cid, seq) None with "[$Hcseq_lb Hcseq_lb_one]") as "#Hcseq_lb2"; eauto.
  iMod (inv_alloc (lockRequestInvN cid seq) _ (LockRequest_inv {| CID:=cid; Seq:=seq; Lockname:=ln |} γrc γlseq γcseq Ps γP) with "[Hrcptsto]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#".
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  iFrame. iExists _. iFrame "#".
Qed.

Lemma Lock_spec ck (srv:loc) (ln:u64) (γrc γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) :
  {{{ own_clerk ck srv γcseq
                ∗ is_lockserver srv γrc γlseq γcseq Ps
  }}}
    Clerk__Lock ck #ln
  {{{ RET #true; own_clerk ck srv γcseq ∗ (Ps ln) }}}.
Proof.
  iIntros (Φ) "[Hclerk #Hsrv] Hpost".
  iNamed "Hclerk".
  rewrite H.
  wp_lam.
  wp_let.
  repeat wp_loadField.
  wp_apply (wp_allocStruct); first eauto.
  iIntros (args0) "Hargs0".
  iDestruct (struct_fields_split with "Hargs0") as "(HCID&HSeq&HLockname&_)".
  iMod (readonly_alloc_1 with "HCID") as "HCID".
  iMod (readonly_alloc_1 with "HSeq") as "HSeq".
  iMod (readonly_alloc_1 with "HLockname") as "HLockname".
  wp_apply wp_ref_to; first eauto.
  iIntros (args_ptrs) "Hargs0_ptr".
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
  iApply fupd_wp.
  iInv replycacheinvN as ">Hrcinv" "HNclose".
  iNamed "Hrcinv".
  destruct (replyHistory !! (cid, seq)) eqn:Hrh.
  {
    iExFalso.
    iDestruct (big_sepM_delete _ _ (cid, seq) with "Hcseq_lb") as "[Hbad _]"; first eauto.
    iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %Hbad.
    iPureIntro. simpl in Hbad.
    lia.
  }
  iMod (map_alloc (cid, seq) None with "Hrcctx") as "[Hrcctx Hrcptsto]"; first done.
  iMod (own_alloc (Excl ())) as "HγP"; first done.
  iDestruct "HγP" as (γP) "HγP".
  iMod (fmcounter_map_update γcseq cid _ (int.nat seq + 1) with "Hcseq_own") as "Hcseq_own".
  { simpl. lia. }
  iMod (fmcounter_map_get_lb with "Hcseq_own") as "[Hcseq_own #Hcseq_lb_one]".
  iDestruct (big_sepM_insert _ _ (cid, seq) None with "[$Hcseq_lb Hcseq_lb_one]") as "#Hcseq_lb2"; eauto.
  iMod (inv_alloc (lockRequestInvN cid seq) _ (LockRequest_inv {| CID:=cid; Seq:=seq; Lockname:=ln |} γrc γlseq γcseq Ps γP) with "[Hrcptsto]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#".
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  Print read_lock_args.
  wp_apply (wp_forBreak
              (fun b => (⌜b = true⌝ ∨ ⌜b = false⌝∗ (Ps ln))
∗ (∃ curr_seq args, 
    let lockArgs := {| CID:=cid; Seq:=curr_seq; Lockname:= ln |} in
     "%" ∷ ⌜lockArgs.(Lockname) = ln⌝
  ∗ "#Hargs" ∷ read_lock_args args lockArgs
  ∗ "#Hargsinv" ∷ (inv (lockRequestInvN lockArgs.(CID) lockArgs.(Seq))
                   (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP))
  ∗ "Hcid" ∷ ck_l ↦[Clerk.S :: "cid"] #cid
  ∗ "Hseq" ∷ (ck_l ↦[Clerk.S :: "seq"] #(LitInt (word.add lockArgs.(Seq) 1)))
  ∗ "Hprimary" ∷ ck_l ↦[Clerk.S :: "primary"] #srv
  ∗ "Hargs_ptr" ∷ args_ptrs ↦[refT (uint64T * (uint64T * (uint64T * unitT))%ht)] #args
  ∗ "Herrb_ptr" ∷ (∃ (err:bool), errb_ptr ↦[boolT] #err)
  ∗ "Hreply" ∷ (∃ lockReply, own_lockreply reply lockReply ∗ (⌜b = true⌝ ∨ ⌜b = false ∧ lockReply.(OK)=true⌝) )
  ∗ "HγP" ∷ (⌜b = false⌝ ∨ own γP (Excl ()))
  ∗ ("Hcseq_own" ∷ cid fm[[γcseq]]↦(int.nat lockArgs.(Seq) + 1))
  ∗ "HΦpost" ∷ (own_clerk #ck_l srv γcseq ∗ Ps ln -∗ Φ #true)
              ))%I with "[] [-]"); eauto.
  {
    iIntros (Ψ).
    iModIntro.
    iIntros "Hpre HΨpost".
    wp_lam.
    iDestruct "Hpre" as "[_ Hpre]".
    iDestruct "Hpre" as (curr_seq args) "Hpre".
    iNamed "Hpre".
    iDestruct "Herrb_ptr" as (err_old) "Herrb_ptr".
    wp_load.
    wp_loadField.
    iDestruct "Hreply" as (lockReply) "Hreply".
    (* TODO: Why does this destruct not work when inside the proof for CalTryLock's pre? *)
    wp_apply (CallTryLock_spec with "[Hreply]"); eauto.
    {
      iSplitL "".
      { iExists _. iFrame "#". }
      iFrame.
      iFrame "#".
      iDestruct "Hreply" as "[Hreply rest]".
      iFrame.
    }

    iIntros (err) "HCallTryLockPost".
    wp_pures.
    iDestruct "HCallTryLockPost" as (lockReply') "[Hreply [% | [% HCallPost]]]".
    { (* No reply from CallTryLock *)
      rewrite H1.
      wp_store.
      wp_load.
      wp_pures.
      iApply "HΨpost".
      iFrame. iSplitL ""; first by iLeft.
      iExists _, _; iFrame; iFrame "#".
      iSplitL ""; first done.
      iSplitL "Herrb_ptr"; eauto.
    }
    { (* Got a reply from CallTryLock *)
      rewrite H1.
      wp_store.
      wp_load.
      wp_pures.
      iNamed "Hreply".
      wp_loadField.
      destruct (lockReply'.(OK)) eqn:Hok.
      { (* Reply granted lock *)
        wp_if.
        wp_pures.
        iApply "HΨpost".
        iSplitL "HγP".
        { iRight. iSplitR "HγP"; first done. simpl.
          admit. (* TODO: open req invariant and exchange γP for P *)
        }
        iExists _, _; iFrame; iFrame "#".
        iSplitL ""; first done.
        iSplitL "Herrb_ptr"; eauto.
        iSplitR ""; last by iLeft.
        iExists _; iFrame. rewrite Hok. iFrame. by iRight.
      }
      { (* Reply indicated lock was already held; allocate new LockArgs and increase seqno to retry *)
        wp_pures.
        repeat wp_loadField.
        wp_apply (wp_allocStruct); eauto.
        iIntros (args') "Hargs'".
        iDestruct (struct_fields_split with "Hargs'") as "(HCID&HSeq&HLockname&_)".
        iMod (readonly_alloc_1 with "HCID") as "#HCID".
        iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
        iMod (readonly_alloc_1 with "HLockname") as "#HLockname".
        wp_store.
        wp_loadField.
        wp_binop.
        wp_storeField.
        iApply "HΨpost".
        iSplitL ""; first by iLeft.
        iExists (word.add curr_seq 1); iFrame "#"; iFrame.
        iNamed "Hargs".
        simpl.
        iExists args'.
        iFrame "#".
        iFrame.
        iSplitL ""; eauto.
        
        iMod (inv_alloc (lockRequestInvN cid seq) _ (LockRequest_inv {| CID:=cid; Seq:=seq; Lockname:=ln |} γrc γlseq γcseq Ps γP) with "[Hrcptsto]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#".
  }
        { unfold read_lock_args.
        iSplitL "Herrb_ptr"; eauto.
        iExists _; iFrame. rewrite Hok. iFrame. by iRight.
      }
    }
  }
  {
    iSplitL ""; first by iLeft.
    iFrame. iSplitL "Herrb_ptr"; eauto.
    iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| OK:= false; Stale:= false |}; iFrame. by iLeft.
  }

  iIntros "LoopPost".
  wp_seq.
  iDestruct "LoopPost" as "(HP & LoopPost)". iNamed "LoopPost".
  iDestruct "Hreply" as (lockReply) "[Hreply %]". iNamed "Hreply".
  wp_loadField.
  destruct H0; first discriminate.
  destruct H0 as [_ ->].
  iApply "Hpost".
  iDestruct "HP" as "[%| [_ HP]]"; first by discriminate.
  iFrame "HP".
  iExists _, _, (word.add seq 1), _; iFrame; iFrame "#".
  iSplitL ""; first done.
  (* TODO: deal with overflow *)
  admit.
Admitted.


Print readonly_def.
End lockservice_proof.
