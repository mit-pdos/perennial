From Perennial.program_proof.lockservice Require Import fmcounter_map nondet.
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

Section rpc.
Context `{!heapG Σ}.

Class RPCRequest (A:Type) :=
  { getCID : A -> u64 ;
    getSeq : A -> u64 ;
    read_args : loc -> A -> iProp Σ
  }.

Class RPCReply R rty_desc := 
  {
  getRet : R -> bool ;
  getStale : R -> bool ;
  own_reply : loc -> R -> iProp Σ ;
  alloc_reply (rloc:loc) : (rloc ↦[struct.t rty_desc] zero_val (struct.t rty_desc)) -∗ (∃r, own_reply rloc r)
  }.


Context `{rpca : RPCRequest A ,
          rpcr : R,
          rpcr_inhabited : Inhabited R
         }.

Context `{fmcounter_mapG Σ}.
Context `{!inG Σ (exclR unitO)}.
Context `{!mapG Σ (u64*u64) (option R)}.

Record TryLockArgsC :=
  mkTryLockArgsC{
  Lockname:u64;
  CID:u64;
  Seq:u64
  }.

Record RPC_GS :=
  mkγrpc {
      rc:gname;
      lseq:gname;
      cseq:gname
    }.

Definition RPCClient_own (cid cseqno:u64) (γrpc:RPC_GS) : iProp Σ :=
  "Hcseq_own" ∷ (cid fm[[γrpc.(cseq)]]↦ int.nat cseqno)
.

Definition RPCServer_own (lastSeqM:gmap u64 u64) lastReplyM γrpc : iProp Σ :=
    ("Hlseq_own" ∷ [∗ map] cid ↦ seq ∈ lastSeqM, cid fm[[γrpc.(lseq)]]↦ int.nat seq)
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
.

Definition RPCReplyReceipt (args:A) (r:R) γrpc : iProp Σ :=
  (args.(getCID), args.(getSeq)) [[γrpc.(rc)]]↦ro Some r
.

Definition RPCRequestStale (args:A) γrpc : iProp Σ :=
  (args.(getCID) fm[[γrpc.(cseq)]]> ((int.nat args.(getSeq)) + 1))
.

Definition RPCRequest_inv (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (args:A) (γrpc:RPC_GS) (γPost:gname) : iProp Σ :=
   "#Hlseq_bound" ∷ args.(getCID) fm[[γrpc.(cseq)]]> int.nat args.(getSeq)
  ∗ ("Hreply" ∷ (args.(getCID), args.(getSeq)) [[γrpc.(rc)]]↦ None ∗ PreCond args ∨
      args.(getCID) fm[[γrpc.(lseq)]]≥ int.nat args.(getSeq)
      ∗ (∃ (last_reply:R), (args.(getCID), args.(getSeq)) [[γrpc.(rc)]]↦ro Some last_reply
        ∗ (own γPost (Excl ()) ∨ PostCond args last_reply)
      )
    ).

Definition ReplyCache_inv (γrpc:RPC_GS) : iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option R),
      ("Hrcctx" ∷ map_ctx γrpc.(rc) 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γrpc.(cseq)]]> int.nat cid_seq.2)
.

Definition replyCacheInvN : namespace := nroot .@ "replyCacheInvN".
Definition rpcRequestInvN := nroot .@ "rpcRequestInvN".

Lemma server_processes_request (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (args:A) (old_seq:u64) (γrpc:RPC_GS) (reply:R)
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
     ((map_get lastSeqM args.(getCID)).1 = old_seq)
  -> (int.val args.(getSeq) > int.val old_seq)%Z
  -> (inv replyCacheInvN (ReplyCache_inv γrpc ))
  -∗ (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond args γrpc γP))
  -∗ PostCond args reply
  -∗ RPCServer_own lastSeqM lastReplyM γrpc
  ={⊤}=∗
      RPCReplyReceipt args reply γrpc
  ∗ RPCServer_own (<[args.(getCID):=args.(getSeq)]> lastSeqM) (<[args.(getCID):=reply]> lastReplyM) γrpc.
Proof.
  intros.
  iIntros "Hlinv HargsInv Hpost Hsown"; iNamed "Hsown".
  iInv "HargsInv" as "[#>Hargseq_lb Hcases]" "HMClose".
  iAssert ((|==> [∗ map] cid↦seq ∈ <[args.(getCID):=old_seq]> lastSeqM, cid fm[[γrpc.(lseq)]]↦int.nat seq)%I) with "[Hlseq_own]" as ">Hlseq_own".
  {
    destruct (map_get lastSeqM args.(getCID)).2 eqn:Hok.
    {
      assert (map_get lastSeqM args.(getCID) = (old_seq, true)) as Hmapget.
      { by apply pair_equal_spec. }
      apply map_get_true in Hmapget.
      rewrite insert_id; eauto.
    }
    {
      assert (map_get lastSeqM args.(getCID) = (old_seq, false)) as Hmapget; first by apply pair_equal_spec.
      iMod (fmcounter_map_alloc 0 γrpc.(lseq) args.(getCID) with "[$]") as "Hlseq_own_new".
      apply map_get_false in Hmapget as [Hnone Hdef].
      simpl in Hdef. rewrite Hdef.
      iDestruct (big_sepM_insert _ _ args.(getCID) with "[$Hlseq_own Hlseq_own_new]") as "Hlseq_own"; eauto.
      replace ((int.nat 0)%Z) with 0 by word.
      done.
    }
  }
  iDestruct "Hcases" as "[[>Hunproc Hpre]|Hproc]".
  {
    iInv replyCacheInvN as ">HNinner" "HNClose".
    iNamed "HNinner".
    iDestruct (map_update _ _ (Some reply) with "Hrcctx Hunproc") as ">[Hrcctx Hrcptsto]".
    iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
    iDestruct (big_sepM_insert_2 _ _ (args.(getCID), args.(getSeq)) (Some reply) with "[Hargseq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    { iNext. iExists _; iFrame; iFrame "#". }

    iDestruct (big_sepM_delete _ _ (args.(getCID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iMod (fmcounter_map_update _ _ _ (int.nat args.(getSeq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
    rewrite ->insert_insert in *.
    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iFrame. iExists _; iFrame "#".
      by iRight.
    }
    iModIntro.

    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM args.(getCID) args.(getSeq) reply with "[Hargseq_lb] Hrcagree") as "Hrcagree2"; eauto.
    iFrame. iFrame "#".
  }
  { (* One-shot update of γrc already happened; this is impossible *)
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (big_sepM_delete _ _ (args.(getCID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.val old_seq) with (Z.of_nat (int.nat old_seq)) in H1; last by apply u64_Z_through_nat.
    replace (int.val args.(getSeq)) with (Z.of_nat (int.nat args.(getSeq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
Qed.

Lemma smaller_seqno_stale_fact (args:A) (lseq:u64) (γrpc:RPC_GS) lastSeqM lastReplyM:
  lastSeqM !! args.(getCID) = Some lseq ->
  (int.val args.(getSeq) < int.val lseq)%Z ->
  inv replyCacheInvN (ReplyCache_inv γrpc) -∗
  RPCServer_own lastSeqM lastReplyM γrpc
    ={⊤}=∗
    RPCServer_own lastSeqM lastReplyM γrpc
    ∗ RPCRequestStale args γrpc.
Proof.
  intros.
  iIntros "#Hinv [Hlseq_own #Hsepm]".
  iInv replyCacheInvN as ">HNinner" "HNclose".
  iNamed "HNinner".
  iDestruct (big_sepM2_dom with "Hsepm") as %Hdomeq.
  assert (is_Some (lastReplyM !! args.(getCID))) as HlastReplyIn.
  { apply elem_of_dom. assert (is_Some (lastSeqM !! args.(getCID))) by eauto. apply elem_of_dom in H2.
    rewrite <- Hdomeq. done. }
  destruct HlastReplyIn as [r HlastReplyIn].
  iDestruct (big_sepM2_delete _ _ _ _ lseq r with "Hsepm") as "[Hptstoro _]"; eauto.
  iDestruct (map_ro_valid with "Hrcctx Hptstoro") as %HinReplyHistory.
  iDestruct (big_sepM_delete _ _ _ with "Hcseq_lb") as "[Hcseq_lb_one _] /="; eauto.
  iDestruct (fmcounter_map_mono_lb (int.nat args.(getSeq) + 2) with "Hcseq_lb_one") as "#HStaleFact".
  { replace (int.val args.(getSeq)) with (Z.of_nat (int.nat args.(getSeq))) in H1; last by apply u64_Z_through_nat.
    replace (int.val lseq) with (Z.of_nat (int.nat lseq)) in H0; last by apply u64_Z_through_nat.
    simpl.
    lia.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  {
    iNext. iExists _; iFrame; iFrame "#".
  }
  iModIntro. replace (int.nat args.(getSeq) + 2) with (int.nat args.(getSeq) + 1 + 1) by lia.
  iFrame; iFrame "#".
Qed.

Lemma alloc_γrc (args:A) γrpc PreCond PostCond:
  (int.nat args.(getSeq)) + 1 = int.nat (word.add args.(getSeq) 1)
  -> inv replyCacheInvN (ReplyCache_inv γrpc )
  -∗ RPCClient_own args.(getCID) args.(getSeq) γrpc
  -∗ PreCond args
  ={⊤}=∗
      RPCClient_own args.(getCID) (word.add args.(getSeq) 1) γrpc
      ∗ (∃ γPost, inv rpcRequestInvN (RPCRequest_inv PreCond PostCond args γrpc γPost) ∗ (own γPost (Excl ()))).
Proof using Type*.
  intros.
  iIntros "Hinv Hcseq_own HPreCond".
  iInv replyCacheInvN as ">Hrcinv" "HNclose".
  iNamed "Hrcinv".
  destruct (replyHistory !! (args.(getCID), args.(getSeq))) eqn:Hrh.
  {
    iExFalso.
    iDestruct (big_sepM_delete _ _ _ with "Hcseq_lb") as "[Hbad _]"; first eauto.
    simpl.
    iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %Hbad.
    iPureIntro. simpl in Hbad.
    lia.
  }
  iMod (map_alloc (args.(getCID), args.(getSeq)) None with "Hrcctx") as "[Hrcctx Hrcptsto]"; first done.
  iMod (own_alloc (Excl ())) as "HγP"; first done.
  iDestruct "HγP" as (γPost) "HγP".
  iMod (fmcounter_map_update γrpc.(cseq) _ _ (int.nat args.(getSeq) + 1) with "Hcseq_own") as "Hcseq_own".
  { simpl. lia. }
  iMod (fmcounter_map_get_lb with "Hcseq_own") as "[Hcseq_own #Hcseq_lb_one]".
  iDestruct (big_sepM_insert _ _ _ None with "[$Hcseq_lb Hcseq_lb_one]") as "#Hcseq_lb2"; eauto.
  iMod (inv_alloc rpcRequestInvN _ (RPCRequest_inv PreCond PostCond args γrpc γPost) with "[Hrcptsto HPreCond]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#". iLeft. iFrame.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  rewrite H0. iFrame. iExists _; iFrame; iFrame "#".
Qed.

Lemma get_request_post (args:A) (r:R) γrpc γPost PreCond PostCond :
  (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond args γrpc γPost))
    -∗ RPCReplyReceipt args r γrpc
    -∗ (own γPost (Excl ()))
    ={⊤}=∗ ▷ (PostCond args r).
Proof using Type*.
  iIntros "#Hinv #Hptstoro HγP".
  iInv rpcRequestInvN as "HMinner" "HMClose".
  iDestruct "HMinner" as "[#>Hlseqbound [[Hbad _] | HMinner]]".
  { iDestruct (ptsto_agree_frac_value with "Hbad [$Hptstoro]") as ">%". destruct H0; discriminate. }
  iDestruct "HMinner" as "[#Hlseq_lb Hrest]".
  iDestruct (later_exist with "Hrest") as "Hrest".
  iDestruct "Hrest" as (last_reply) "[Hptstoro_some [>Hbad | HP]]".
  { by iDestruct (own_valid_2 with "HγP Hbad") as %Hbad. }
  iMod ("HMClose" with "[HγP]") as "_".
  { iNext. iFrame "#". iRight. iExists r. iFrame "#". iLeft. done. }
  iModIntro. iModIntro.
  iDestruct (ptsto_ro_agree with "Hptstoro_some Hptstoro") as %Heq.
  by injection Heq as ->.
Qed.

Context `{ rpcr_into_val : into_val.IntoVal R}.
Lemma server_replies_to_request (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (args:A) (γrpc:RPC_GS) (reply:R)
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
     (lastSeqM !! args.(getCID) = Some args.(getSeq))
  -> (inv replyCacheInvN (ReplyCache_inv γrpc ))
  -∗ (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond args γrpc γP))
  -∗ RPCServer_own lastSeqM lastReplyM γrpc
  ={⊤}=∗
      RPCReplyReceipt args reply γrpc
  ∗ RPCServer_own (lastSeqM) (lastReplyM) γrpc.
Proof.
  intros Hsome [ok Hreplymapget].
  iIntros "Hlinv HargsInv Hpost Hsown"; iNamed "Hsown".
  iAssert ⌜ok = true⌝%I as %->.
  { iDestruct (big_sepM2_lookup_1 _ _ _ args.(getCID) with "Hrcagree") as "HH"; eauto.
    iDestruct "HH" as (x B) "H".
    simpl. iPureIntro. unfold map_get in Hreplymapget.
    revert Hreplymapget.
    rewrite B. simpl. intros. injection Hreplymapget. done.
    (* TODO: get a better proof of this... *)
  }
  apply map_get_true in Hreplymapget.
  iDestruct (big_sepM2_delete with "Hrcagree") as "[#Hrcptsto _]"; eauto.
  iModIntro.
  iFrame "#"; iFrame.
Qed.

End rpc.
