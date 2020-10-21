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

Context {A:Type}.

Record RPCRequest :=
{
  CID : u64 ;
  Seq : u64 ;
  Args : A ;
}.

Context {R:Type}.

Record RPCReply :=
{
  Stale : bool ;
  Ret : R ;
}.

Context `{fmcounter_mapG Σ}.
Context `{!inG Σ (exclR unitO)}.
Context `{!mapG Σ (u64*u64) (option R)}.

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

Definition RPCReplyReceipt (req:RPCRequest) (r:R) γrpc : iProp Σ :=
  (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ro Some r
.

Definition RPCRequestProcessing (req:RPCRequest) γrpc lastSeqM lastReplyM : iProp Σ :=
  ("Hprocessing_ptsto" ∷ (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦{1/2} None)
  ∗ ("Hlseq_own" ∷ [∗ map] cid ↦ seq ∈ <[req.(CID):=req.(Seq)]> lastSeqM, cid fm[[γrpc.(lseq)]]↦ int.nat seq)
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
.

Definition RPCRequestStale (req:RPCRequest) γrpc : iProp Σ :=
  (req.(CID) fm[[γrpc.(cseq)]]> ((int.nat req.(Seq)) + 1))
.

Definition RPCRequest_inv (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (req:RPCRequest) (γrpc:RPC_GS) (γPost:gname) : iProp Σ :=
   "#Hlseq_bound" ∷ req.(CID) fm[[γrpc.(cseq)]]> int.nat req.(Seq)
    ∗ ( (* Initialized, but server has not started processing *)
      "Hreply" ∷ (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ None ∗ PreCond req.(Args) ∨ 

      (* Server has started processing, but not finished *)
       req.(CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Seq)
      ∗ "Hreply" ∷ (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦{1/2} None
      ∨

      (* Server has finished processing; two sub-states for wether client has taken PostCond out *)
      req.(CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Seq)
      ∗ (∃ (last_reply:R), (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ro Some last_reply
        ∗ (own γPost (Excl ()) ∨ PostCond req.(Args) last_reply)
      )
    ).

Definition ReplyCache_inv (γrpc:RPC_GS) : iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option R),
      ("Hrcctx" ∷ map_ctx γrpc.(rc) 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γrpc.(cseq)]]> int.nat cid_seq.2)
.

Definition replyCacheInvN : namespace := nroot .@ "replyCacheInvN".
Definition rpcRequestInvN := nroot .@ "rpcRequestInvN".

Lemma server_takes_request (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (req:RPCRequest) (old_seq:u64) (γrpc:RPC_GS)
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
     ((map_get lastSeqM req.(CID)).1 = old_seq)
  -> (int.val req.(Seq) > int.val old_seq)%Z
  -> (inv replyCacheInvN (ReplyCache_inv γrpc ))
  -∗ (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γP))
  -∗ RPCServer_own lastSeqM lastReplyM γrpc
  ={⊤}=∗
      ▷ PreCond req.(Args)
      ∗ RPCRequestProcessing req γrpc lastSeqM lastReplyM.
Proof.
  intros.
  iIntros "Hlinv HreqInv Hsown"; iNamed "Hsown".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iAssert ((|==> [∗ map] cid↦seq ∈ <[req.(CID):=old_seq]> lastSeqM, cid fm[[γrpc.(lseq)]]↦int.nat seq)%I) with "[Hlseq_own]" as ">Hlseq_own".
  {
    destruct (map_get lastSeqM req.(CID)).2 eqn:Hok.
    {
      assert (map_get lastSeqM req.(CID) = (old_seq, true)) as Hmapget.
      { by apply pair_equal_spec. }
      apply map_get_true in Hmapget.
      rewrite insert_id; eauto.
    }
    {
      assert (map_get lastSeqM req.(CID) = (old_seq, false)) as Hmapget; first by apply pair_equal_spec.
      iMod (fmcounter_map_alloc 0 γrpc.(lseq) req.(CID) with "[$]") as "Hlseq_own_new".
      apply map_get_false in Hmapget as [Hnone Hdef].
      simpl in Hdef. rewrite Hdef.
      iDestruct (big_sepM_insert _ _ req.(CID) with "[$Hlseq_own Hlseq_own_new]") as "Hlseq_own"; eauto.
      replace ((int.nat 0)%Z) with 0 by word.
      done.
    }
  }
  iDestruct "Hcases" as "[[>Hunproc Hpre]|[Hproc|Hproc]]".
  {
    iDestruct "Hunproc" as "[Hunproc_inv Hunproc]".
    iDestruct (big_sepM_delete _ _ (req.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iMod (fmcounter_map_update _ _ _ (int.nat req.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
    rewrite ->insert_insert in *.
    iMod ("HMClose" with "[Hunproc_inv]") as "_"; eauto.
    {
      iNext. iFrame "#". iRight. iLeft. iFrame.
    }
    iModIntro.
    iFrame; iFrame "#".
  }
  {
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (big_sepM_delete _ _ (req.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.val old_seq) with (Z.of_nat (int.nat old_seq)) in H1; last by apply u64_Z_through_nat.
    replace (int.val req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
  {
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (big_sepM_delete _ _ (req.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.val old_seq) with (Z.of_nat (int.nat old_seq)) in H1; last by apply u64_Z_through_nat.
    replace (int.val req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
Qed.

Lemma server_completes_request {_:Inhabited R} (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (req:RPCRequest) (γrpc:RPC_GS) (reply:R)
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
  (inv replyCacheInvN (ReplyCache_inv γrpc ))
  -∗ (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γP))
  -∗ PostCond req.(Args) reply
  -∗ RPCRequestProcessing req γrpc lastSeqM lastReplyM
  ={⊤}=∗
      RPCReplyReceipt req reply γrpc
  ∗ RPCServer_own (<[req.(CID):=req.(Seq)]> lastSeqM) (<[req.(CID):=reply]> lastReplyM) γrpc.
Proof using Type*.
  intros.
  iIntros "Hlinv HreqInv Hpost Hprocessing"; iNamed "Hprocessing".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iDestruct "Hcases" as "[[>Hunproc Hpre]|[>Hproc|Hprocessed]]".
  {
    iDestruct (ptsto_agree_frac_value with "Hprocessing_ptsto Hunproc") as %[_ Hbad].
    contradiction.
  }
  {
    iInv replyCacheInvN as ">HNinner" "HNClose".
    iNamed "HNinner".
    iDestruct "Hproc" as "[_ Hproc]".
    iCombine "Hproc Hprocessing_ptsto" as "Hptsto".
    iDestruct (map_update _ _ (Some reply) with "Hrcctx Hptsto") as ">[Hrcctx Hrcptsto]".
    iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
    iDestruct (big_sepM_insert_2 _ _ (req.(CID), req.(Seq)) (Some reply) with "[Hreqeq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    { iNext. iExists _; iFrame; iFrame "#". }

    iDestruct (big_sepM_delete _ _ (req.(CID)) _ with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply lookup_insert.
    iMod (fmcounter_map_update _ _ _ (int.nat req.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iDestruct (big_sepM_insert_delete with "[$Hlseq_own $Hlseq_one]") as "Hlseq_own".
    rewrite ->insert_insert in *.
    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iRight. iFrame. iExists _; iFrame "#".
      by iRight.
    }
    iModIntro.

    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM req.(CID) req.(Seq) reply with "[Hreqeq_lb] Hrcagree") as "Hrcagree2"; eauto.
    iFrame. iFrame "#".
  }
  { (* One-shot update of γrc already happened; this is impossible *)
    iDestruct "Hprocessed" as "[_ Hbadptsto]".
    iDestruct "Hbadptsto" as (a) "[>Hbadptsto _]".
    iDestruct (ptsto_agree_frac_value with "Hbadptsto Hprocessing_ptsto") as %[Hbad _]; done.
  }
Qed.

Lemma smaller_seqno_stale_fact (req:RPCRequest) (lseq:u64) (γrpc:RPC_GS) lastSeqM lastReplyM:
  lastSeqM !! req.(CID) = Some lseq ->
  (int.val req.(Seq) < int.val lseq)%Z ->
  inv replyCacheInvN (ReplyCache_inv γrpc) -∗
  RPCServer_own lastSeqM lastReplyM γrpc
    ={⊤}=∗
    RPCServer_own lastSeqM lastReplyM γrpc
    ∗ RPCRequestStale req γrpc.
Proof.
  intros HlastSeqSome Hineq.
  iIntros "#Hinv [Hlseq_own #Hsepm]".
  iInv replyCacheInvN as ">HNinner" "HNclose".
  iNamed "HNinner".
  iDestruct (big_sepM2_dom with "Hsepm") as %Hdomeq.
  assert (is_Some (lastReplyM !! req.(CID))) as HlastReplyIn.
  { apply elem_of_dom. assert (is_Some (lastSeqM !! req.(CID))) as HlastSeqSome2 by eauto. apply elem_of_dom in HlastSeqSome2.
    rewrite <- Hdomeq. done. }
  destruct HlastReplyIn as [r HlastReplyIn].
  iDestruct (big_sepM2_delete _ _ _ _ lseq r with "Hsepm") as "[Hptstoro _]"; eauto.
  iDestruct (map_ro_valid with "Hrcctx Hptstoro") as %HinReplyHistory.
  iDestruct (big_sepM_delete _ _ _ with "Hcseq_lb") as "[Hcseq_lb_one _] /="; eauto.
  iDestruct (fmcounter_map_mono_lb (int.nat req.(Seq) + 2) with "Hcseq_lb_one") as "#HStaleFact".
  { replace (int.val req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hineq; last by apply u64_Z_through_nat.
    simpl.
    lia.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  {
    iNext. iExists _; iFrame; iFrame "#".
  }
  iModIntro. replace (int.nat req.(Seq) + 2) with (int.nat req.(Seq) + 1 + 1) by lia.
  iFrame; iFrame "#".
Qed.

Lemma alloc_γrc (req:RPCRequest) γrpc PreCond PostCond:
  (int.nat req.(Seq)) + 1 = int.nat (word.add req.(Seq) 1)
  -> inv replyCacheInvN (ReplyCache_inv γrpc )
  -∗ RPCClient_own req.(CID) req.(Seq) γrpc
  -∗ PreCond req.(Args)
  ={⊤}=∗
      RPCClient_own req.(CID) (word.add req.(Seq) 1) γrpc
      ∗ (∃ γPost, inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γPost) ∗ (own γPost (Excl ()))).
Proof using Type*.
  intros Hsafeincr.
  iIntros "Hinv Hcseq_own HPreCond".
  iInv replyCacheInvN as ">Hrcinv" "HNclose".
  iNamed "Hrcinv".
  destruct (replyHistory !! (req.(CID), req.(Seq))) eqn:Hrh.
  {
    iExFalso.
    iDestruct (big_sepM_delete _ _ _ with "Hcseq_lb") as "[Hbad _]"; first eauto.
    simpl.
    iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %Hbad.
    iPureIntro. simpl in Hbad.
    lia.
  }
  iMod (map_alloc (req.(CID), req.(Seq)) None with "Hrcctx") as "[Hrcctx Hrcptsto]"; first done.
  iMod (own_alloc (Excl ())) as "HγP"; first done.
  iDestruct "HγP" as (γPost) "HγP".
  iMod (fmcounter_map_update γrpc.(cseq) _ _ (int.nat req.(Seq) + 1) with "Hcseq_own") as "Hcseq_own".
  { simpl. lia. }
  iMod (fmcounter_map_get_lb with "Hcseq_own") as "[Hcseq_own #Hcseq_lb_one]".
  iDestruct (big_sepM_insert _ _ _ None with "[$Hcseq_lb Hcseq_lb_one]") as "#Hcseq_lb2"; eauto.
  iMod (inv_alloc rpcRequestInvN _ (RPCRequest_inv PreCond PostCond req γrpc γPost) with "[Hrcptsto HPreCond]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#". iLeft. iFrame.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  rewrite Hsafeincr. iFrame. iExists _; iFrame; iFrame "#".
Qed.

Lemma get_request_post {_:Inhabited R} (req:RPCRequest) (r:R) γrpc γPost PreCond PostCond :
  (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γPost))
    -∗ RPCReplyReceipt req r γrpc
    -∗ (own γPost (Excl ()))
    ={⊤}=∗ ▷ (PostCond req.(Args) r).
Proof using Type*.
  iIntros "#Hinv #Hptstoro HγP".
  iInv rpcRequestInvN as "HMinner" "HMClose".
  iDestruct "HMinner" as "[#>Hlseqbound [[Hbad _] | [[_ >Hbad] | HMinner]]]".
  { iDestruct (ptsto_agree_frac_value with "Hbad [$Hptstoro]") as ">%". destruct H0; discriminate. }
  { iDestruct (ptsto_agree_frac_value with "Hbad [$Hptstoro]") as %Hbad. destruct Hbad; discriminate. }
  iDestruct "HMinner" as "[#Hlseq_lb Hrest]".
  iDestruct (later_exist with "Hrest") as "Hrest".
  iDestruct "Hrest" as (last_reply) "[Hptstoro_some [>Hbad | HP]]".
  { by iDestruct (own_valid_2 with "HγP Hbad") as %Hbad. }
  iMod ("HMClose" with "[HγP]") as "_".
  { iNext. iFrame "#". iRight. iRight. iExists r. iFrame "#". iLeft. done. }
  iModIntro. iModIntro.
  iDestruct (ptsto_ro_agree with "Hptstoro_some Hptstoro") as %Heq.
  by injection Heq as ->.
Qed.

Lemma server_replies_to_request {_:into_val.IntoVal R} (PreCond  : A -> iProp Σ) (PostCond  : A -> R -> iProp Σ) (req:RPCRequest) (γrpc:RPC_GS) (reply:R)
      (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
     (lastSeqM !! req.(CID) = Some req.(Seq))
  -> (∃ ok, map_get lastReplyM req.(CID) = (reply, ok))
  -> (inv replyCacheInvN (ReplyCache_inv γrpc ))
  -∗ (inv rpcRequestInvN (RPCRequest_inv PreCond PostCond req γrpc γP))
  -∗ RPCServer_own lastSeqM lastReplyM γrpc
  ={⊤}=∗
      RPCReplyReceipt req reply γrpc
  ∗ RPCServer_own (lastSeqM) (lastReplyM) γrpc.
Proof.
  intros Hsome [ok Hreplymapget].
  iIntros "Hlinv HreqInv Hsown"; iNamed "Hsown".
  iAssert ⌜ok = true⌝%I as %->.
  { iDestruct (big_sepM2_lookup_1 _ _ _ req.(CID) with "Hrcagree") as "HH"; eauto.
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
