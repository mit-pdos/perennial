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

Lemma fmcounter_map_mono_lb n1 n2 γ k :
  n1 ≤ n2 ->
  k fm[[γ]]≥ n2 -∗ k fm[[γ]]≥ n1.
Admitted.

(* TODO: in the real fmcounter_map, this will need some preconditions *)
Lemma fmcounter_map_alloc n γ k :
  True
  ={⊤}=∗ k fm[[γ]]↦ n.
Admitted.


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
    ∗ ("Hlockeds" ∷ [∗ map] ln ↦ locked ; _ ∈ locksM ; validLocknames, (⌜locked=true⌝ ∨ (Ps ln)))
    
    ∗ ("Hlseq_own" ∷ [∗ map] cid ↦ seq ∈ lastSeqM, cid fm[[γlseq]]↦ int.nat seq)
    ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrc]]↦ro Some r)
.

(* Should make this readonly so it can be read by the RPC background thread *)
Definition read_lock_args (args_ptr:loc) (lockArgs:LockArgsC): iProp Σ :=
  "#HLocknameValid" ∷ ⌜is_Some (validLocknames !! lockArgs.(Lockname))⌝
  ∗ "#HSeqPositive" ∷ ⌜int.nat lockArgs.(Seq) > 0⌝
  ∗ "#HLockArgsOwnLockname" ∷ readonly (args_ptr ↦[LockArgs.S :: "Lockname"] #lockArgs.(Lockname))
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

Lemma server_processes_request (lockArgs:LockArgsC) (old_seq:u64) (γrc γcseq γlseq:gname) (r:bool) (Ps: u64 -> (iProp Σ))
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 bool) γP :
     (int.val lockArgs.(Seq) > int.val old_seq)%Z
  -> (inv replycacheinvN (ReplyCache_inv γrc γcseq Ps ))
  -∗ (inv (lockRequestInvN lockArgs.(CID) lockArgs.(Seq)) (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP))
  -∗ ⌜r = false⌝ ∨ ⌜r = true⌝ ∗ Ps lockArgs.(Lockname)
  -∗ ([∗ map] cid↦seq ∈ <[lockArgs.(CID):=old_seq]> lastSeqM, cid fm[[γlseq]]↦ int.nat seq)
  -∗ ([∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrc]]↦ro Some r)
  ={⊤}=∗
    (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro Some r
  ∗ ([∗ map] cid↦seq ∈ <[lockArgs.(CID):=lockArgs.(Seq)]> lastSeqM, cid fm[[γlseq]]↦ int.nat seq)
  ∗ ([∗ map] cid↦seq;y ∈ <[lockArgs.(CID):=lockArgs.(Seq)]> lastSeqM;
                <[lockArgs.(CID):=r]> lastReplyM, 
                (cid, seq) [[γrc]]↦ro Some y).
Proof using mapG1.
  intros.
  iIntros "Hlinv HargsInv Hpost Hlseq_own #Hrcagree".
  iInv "HargsInv" as "[#>Hargseq_lb Hcases]" "HMClose".
  iDestruct "Hcases" as "[>Hunproc|Hproc]".
  {
    iInv replycacheinvN as ">HNinner" "HNClose".
    (* Give unique namespaces to invariants *)
    iNamed "HNinner".
    iDestruct (map_update _ _ (Some r) with "Hrcctx Hunproc") as ">[Hrcctx Hrcptsto]".
    iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
    iDestruct (big_sepM_insert_2 _ _ (lockArgs.(CID), lockArgs.(Seq)) (Some r) with "[Hargseq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    { iNext. iExists _; iFrame; iFrame "#". }

    iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iMod (fmcounter_map_update _ _ _ (int.nat lockArgs.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
    rewrite ->insert_insert in *.
    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iFrame. iExists _; iFrame "#".
      iDestruct "Hpost" as "[Hpost|[% Hpost]]".
      - by iLeft.
      - by iRight; iLeft.
    }
    iModIntro.

    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM lockArgs.(CID) lockArgs.(Seq) r with "[Hargseq_lb] Hrcagree") as "Hrcagree2"; eauto.
  }
  { (* One-shot update of γrc already happened; this is impossible *)
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (big_sepM_delete _ _ (lockArgs.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.val old_seq) with (Z.of_nat (int.nat old_seq)) in H; last by apply u64_Z_through_nat.
    replace (int.val lockArgs.(Seq)) with (Z.of_nat (int.nat lockArgs.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
Qed.
            
Lemma smaller_seqno_stale_fact (seq lseq cid :u64) γrc γcseq Ps lastSeqM lastReplyM:
  lastSeqM !! cid = Some lseq ->
  (int.val seq < int.val lseq)%Z ->
  inv replycacheinvN (ReplyCache_inv γrc γcseq Ps) -∗
  ([∗ map] cid↦seq;r ∈ lastSeqM;lastReplyM, (cid, seq) [[γrc]]↦ro Some r)
    ={⊤}=∗
  cid fm[[γcseq]]>(int.nat seq + 1).
Proof using inG0 mapG1.
  intros.
  iIntros "#Hinv #Hsepm".
  iInv replycacheinvN as ">HNinner" "HNclose".
  iNamed "HNinner".
  iDestruct (big_sepM2_dom with "Hsepm") as %Hdomeq.
  assert (is_Some (lastReplyM !! cid)) as HlastReplyIn.
  { apply elem_of_dom. assert (is_Some (lastSeqM !! cid)) by eauto. apply elem_of_dom in H1.
    rewrite <- Hdomeq. done. }
  Check big_sepM_delete.
  destruct HlastReplyIn as [r HlastReplyIn].
  iDestruct (big_sepM2_delete _ _ _ cid lseq r with "Hsepm") as "[Hptstoro _]"; eauto.
  iDestruct (map_ro_valid with "Hrcctx Hptstoro") as %HinReplyHistory.
  iDestruct (big_sepM_delete _ _ (cid, lseq) with "Hcseq_lb") as "[Hcseq_lb_one _] /="; eauto.
  iDestruct (fmcounter_map_mono_lb (int.nat seq + 2) with "Hcseq_lb_one") as "#HStaleFact".
  { replace (int.val seq) with (Z.of_nat (int.nat seq)) in H0; last by apply u64_Z_through_nat.
    replace (int.val lseq) with (Z.of_nat (int.nat lseq)) in H0; last by apply u64_Z_through_nat.
    lia.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  {
    iNext. iExists _; iFrame; iFrame "#".
  }
  iModIntro. by replace (int.nat seq + 2) with (int.nat seq + 1 + 1) by lia.
Qed.

Lemma TryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) (γrc γi γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) γP :
  {{{ "#Hls" ∷ is_lockserver srv γrc γlseq γcseq Ps
      ∗ "#HargsInv" ∷ inv (lockRequestInvN lockArgs.(CID) lockArgs.(Seq)) (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
LockServer__TryLock #srv #args #reply
{{{ RET #false; ∃ lockReply', own_lockreply reply lockReply'
    ∗ (⌜lockReply'.(Stale) = true⌝ ∗ (lockArgs.(CID) fm[[γcseq]]> ((int.nat lockArgs.(Seq)) + 1))
  ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro (Some lockReply'.(OK)))
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
readonly (args ↦[LockArgs.S :: "Seq"] #lockArgs.(Seq))
∗ ⌜int.nat lockArgs.(Seq) > 0⌝
         ∗ ([∗ map] cid↦seq ∈ lastSeqM, cid fm[[γlseq]]↦int.nat seq)
}}}
  if: #ok then #v ≥ struct.loadF LockArgs.S "Seq" #args
         else #false
{{{ ifr, RET ifr; ∃b:bool, ⌜ifr = #b⌝
  ∗ ((⌜b = false⌝ ∗ ⌜int.nat v < int.nat lockArgs.(Seq)⌝
     ∗ ([∗ map] cid↦seq ∈ <[lockArgs.(CID):=v]> lastSeqM, cid fm[[γlseq]]↦int.nat seq)) ∨

     (⌜b = true⌝ ∗  ⌜(int.val lockArgs.(Seq) ≤ int.val v ∧ ok=true)%Z⌝
     ∗ ([∗ map] cid↦seq ∈ lastSeqM, cid fm[[γlseq]]↦int.nat seq)
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
      iMod (fmcounter_map_alloc 0 γlseq lockArgs.(CID) with "[$]") as "Hlseq_own_new".
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
        iMod (server_processes_request _ _ _ _ _ false with "Hlinv HargsInv [] Hlseq_own Hrcagree") as "(#Hrcptsoro & Hlseq_own & #Hrcagree2)"; eauto.
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

Lemma CallTryLock_spec (srv args reply:loc) (lockArgs:LockArgsC) (lockReply:LockReplyC) (γrc γi γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) γP :
  {{{ "#Hls" ∷ is_lockserver srv γrc γlseq γcseq Ps
      ∗ "#HargsInv" ∷ inv (lockRequestInvN lockArgs.(CID) lockArgs.(Seq)) (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP)
      ∗ "#Hargs" ∷ read_lock_args args lockArgs
      ∗ "Hreply" ∷ own_lockreply reply lockReply
  }}}
CallTryLock #srv #args #reply
{{{ e, RET e;
    (∃ lockReply', own_lockreply reply lockReply'
    ∗ (⌜e = #true⌝ ∨ ⌜e = #false⌝ ∗ (⌜lockReply'.(Stale) = true⌝ ∗ (lockArgs.(CID) fm[[γcseq]]> (int.nat lockArgs.(Seq) + 1)) ∨ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro (Some lockReply'.(OK)))))
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


Lemma alloc_γrc (cid seq ln:u64) γrc γlseq γcseq Ps:
  inv replycacheinvN (ReplyCache_inv γrc γcseq Ps)
      ∗ cid fm[[γcseq]]↦ int.nat seq
  ={⊤}=∗
      cid fm[[γcseq]]↦ (int.nat seq + 1)
      ∗ (∃ γP, inv (lockRequestInvN cid seq) (LockRequest_inv {| CID:=cid; Seq:=seq; Lockname:= ln |} γrc γlseq γcseq Ps γP) ∗ (own γP (Excl ()))).
Proof using mapG1.
  (* WHY: Why is the above necessary? *)
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
  iFrame. iExists _; iFrame; iFrame "#".
Qed.

Lemma getP_RequestInv_γrc (lockArgs:LockArgsC) γrc γlseq γcseq Ps γP M:
  (inv M (LockRequest_inv lockArgs γrc γlseq γcseq Ps γP))
    -∗ (lockArgs.(CID), lockArgs.(Seq)) [[γrc]]↦ro Some true
    -∗ (own γP (Excl ()))
    ={⊤}=∗ ▷ Ps lockArgs.(Lockname).
Proof.
  iIntros "#Hinv #Hptstoro HγP".
  iInv M as "HMinner" "HMClose".
  iDestruct "HMinner" as "[#>Hlseqbound [Hbad | HMinner]]".
  { iDestruct (ptsto_agree_frac_value with "Hbad [$Hptstoro]") as ">%". destruct H; discriminate. }
  iDestruct "HMinner" as "[#Hlseq_lb Hrest]".
  iDestruct "Hrest" as (last_reply) "[Hptstoro_some [#>Hre | HP]]".
  { iDestruct "Hre" as %->.
    iDestruct (ptsto_agree_frac_value with "Hptstoro_some [$Hptstoro]") as ">%". destruct H; discriminate. }
  iDestruct "HP" as "[HP|>Hbad]".
  {
    iMod ("HMClose" with "[HγP]").
    { iNext. iFrame "#". iRight. iExists true. iFrame "#". iRight; iRight. done. }
    done.
  }
  { by iDestruct (own_valid_2 with "HγP Hbad") as %Hbad. }
Qed.

Lemma Lock_spec ck (srv:loc) (ln:u64) (γrc γlseq γcseq:gname) (Ps: u64 -> (iProp Σ)) :
  {{{
       ⌜is_Some (validLocknames !! ln)⌝
      ∗ own_clerk ck srv γcseq
      ∗ is_lockserver srv γrc γlseq γcseq Ps
  }}}
    Clerk__Lock ck #ln
  {{{ RET #true; own_clerk ck srv γcseq ∗ (Ps ln) }}}.
Proof.
  iIntros (Φ) "[% [Hclerk #Hsrv]] Hpost".
  iNamed "Hclerk".
  rewrite H0.
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
  iMod (alloc_γrc with "[$Hcseq_own $Hlinv]") as "[Hcseq_own HallocPost]".
  iDestruct "HallocPost" as (γP0) "[#Hreqinv_init HγP0]".
  wp_apply (wp_forBreak
              (fun b => (⌜b = true⌝ ∨ ⌜b = false⌝∗ (Ps ln))
∗ (∃ curr_seq args γP, 
    let lockArgs := {| CID:=cid; Seq:=curr_seq; Lockname:= ln |} in
    "#Hargs" ∷ read_lock_args args lockArgs
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
    (* WHY: Why does this destruct not work when inside the proof for CalTryLock's pre? *)
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
    iDestruct "HCallTryLockPost" as (lockReply') "[Hreply [#Hre | [#Hre HCallPost]]]".
    { (* No reply from CallTryLock *)
      iDestruct "Hre" as %->.
      wp_store.
      wp_load.
      wp_pures.
      iApply "HΨpost".
      iFrame. iSplitL ""; first by iLeft.
      iExists _, _, _; iFrame; iFrame "#".
      iSplitL "Herrb_ptr"; eauto.
    }
    { (* Got a reply from CallTryLock *)
      iDestruct "Hre" as %->.
      wp_store.
      wp_load.
      wp_pures.
      iNamed "Hreply".
      wp_loadField.
      destruct (lockReply'.(OK)) eqn:Hok.
      { (* Reply granted lock *)
        iDestruct "HCallPost" as "[Hbad | #Hrcptstoro]"; simpl.
        { iDestruct "Hbad" as "[_ Hbad]".
          iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %bad.
          lia.
        }
        iDestruct "HγP" as "[%|HγP]"; first discriminate.
        iMod (getP_RequestInv_γrc with "Hargsinv Hrcptstoro HγP") as "HP /=".
        wp_pures.
        iApply "HΨpost".
        iSplitL "HP".
        { iRight. by iFrame. }
        iExists _, _, _; iFrame; iFrame "#".
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

        simpl.
        replace (int.nat curr_seq + 1) with (int.nat (word.add curr_seq 1)).
        2: {
         admit. (* Deal with overflow *)
        }
        iMod (alloc_γrc cid with "[$Hlinv $Hcseq_own]") as "[Hcseq_own HallocPost]".
        iDestruct "HallocPost" as (γP') "[#Hreqinv_new HγP']".
        wp_storeField.
        iApply "HΨpost".
        iSplitL ""; first by iLeft.
        iExists (word.add curr_seq 1); iFrame "#"; iFrame.
        iNamed "Hargs".
        simpl.
        iExists args', γP'.
        iFrame "#".
        iFrame.
        iSplitL "Herrb_ptr"; eauto.
        iExists _; iFrame. rewrite Hok. iFrame. by iLeft.
      }
    }
  }
  {
    iSplitL ""; first by iLeft.
    iExists _, _, _; iFrame; iFrame "#".
    iSplitL ""; first done.
    iSplitL "Herrb_ptr"; eauto.
    iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| OK:=false; Stale:=false |}; iFrame. by iLeft.
  }

  iIntros "LoopPost".
  wp_seq.
  iDestruct "LoopPost" as "(HP & LoopPost)". iNamed "LoopPost".
  iDestruct "Hreply" as (lockReply) "[Hreply %]". iNamed "Hreply".
  wp_loadField.
  destruct H1; first discriminate.
  destruct H1 as [_ ->].
  iApply "HΦpost".
  iDestruct "HP" as "[%| [_ HP]]"; first by discriminate.
  iFrame "HP".
  iExists _, _, (word.add seq 1), _; iFrame; iFrame "#".
  iSplitL ""; first done.
  (* TODO: deal with overflow *)
  admit.
Admitted.

End lockservice_proof.
