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

(** Colelcting the CMRAs we need. *)
Class rpcG Σ (R : Type) := RpcG {
  rpc_fmcounterG :> fmcounter_mapG Σ;
  rpc_escrowG :> inG Σ (exclR unitO);
  rpc_mapG :> mapG Σ (u64*u64) (option R);
}.
(* FIXME: add subΣ instance. *)

Section rpc.
Context `{!heapG Σ}.
Context {A:Type} {R:Type}.
Context `{!rpcG Σ R}.


(* FIXME: move upstream *)
Section gset.
  Context `{Countable T}.
  Implicit Types X : gset T.
  Implicit Types Φ : T → iProp Σ.

  Lemma big_sepS_elem_of_acc_impl x Φ X :
    x ∈ X →
    ([∗ set] y ∈ X, Φ y) -∗ Φ x ∗
      (∀ Ψ, Ψ x -∗ □ (∀ y, ⌜y ∈ X ∧ y ≠ x⌝ -∗ Φ y -∗ Ψ y) -∗ ([∗ set] y ∈ X, Ψ y)).
  Proof.
  Admitted.

End gset.

Record RPCRequest :=
{
  CID : u64 ;
  Seq : u64 ;
  Args : A ;
}.

Record RPCReply :=
{
  Stale : bool ;
  Ret : R ;
}.

(** RPC layer ghost names. *)
Record rpc_names :=
  RpcNames {
      rc:gname; (* full reply history: tracks the reply for every (CID, SEQ) pair that exists, where [None] means "reply not yet determined" *)
      lseq:gname; (* latest sequence number for each client seen by server *)
      cseq:gname (* next sequence number to be used by each client (i.e., one ahead of the latest that it used *)
    }.

Definition RPCClient_own (γrpc:rpc_names) (cid cseqno:u64) : iProp Σ :=
  "Hcseq_own" ∷ (cid fm[[γrpc.(cseq)]]↦ int.nat cseqno)
.

(** Ownership of *all* the server-side sequence number tracking tokens *)
Definition RPCServer_lseq γrpc (lastSeqM:gmap u64 u64) : iProp Σ :=
  ([∗ set] cid ∈ (fin_to_set u64), cid fm[[γrpc.(lseq)]]↦ int.nat (default (U64 0) (lastSeqM !! cid)))%I.

Definition RPCServer_own γrpc (lastSeqM:gmap u64 u64) lastReplyM : iProp Σ :=
    "Hlseq_own" ∷ RPCServer_lseq γrpc lastSeqM
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
.

Definition RPCReplyReceipt γrpc (req:RPCRequest) (r:R) : iProp Σ :=
  (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦ro Some r
.

Definition RPCRequestProcessing γrpc (req:RPCRequest) (lastSeqM:gmap u64 u64) lastReplyM : iProp Σ :=
  ("Hprocessing_ptsto" ∷ (req.(CID), req.(Seq)) [[γrpc.(rc)]]↦{1/2} None) ∗
  ("Hlseq_own" ∷ RPCServer_lseq γrpc (<[req.(CID):=req.(Seq)]> lastSeqM)) ∗
  ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
.

Definition RPCRequestStale γrpc (req:RPCRequest) : iProp Σ :=
  (req.(CID) fm[[γrpc.(cseq)]]> ((int.nat req.(Seq)) + 1))
.

(** The per-request invariant has 4 states.
initialized: Request created and "on its way" to the server.
processing: The server received the request and is computing the reply.
done: The reply was computed as is waiting for the client to take notice.
dead: The client took out ownership of the reply. *)
Local Definition RPCRequest_inv (γrpc:rpc_names) (γPost:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
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

Local Definition ReplyTable_inv (γrpc:rpc_names) : iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option R),
      ("Hrcctx" ∷ map_ctx γrpc.(rc) 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γrpc.(cseq)]]> int.nat cid_seq.2)
.

Definition replyTableInvN : namespace := nroot .@ "replyTableInvN".
Definition rpcRequestInvN := nroot .@ "rpcRequestInvN".

Definition is_RPCRequest (γrpc:rpc_names) (γPost:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
  inv rpcRequestInvN (RPCRequest_inv γrpc γPost PreCond PostCond req).
Definition RPCRequest_token (γPost:gname) : iProp Σ :=
  (own γPost (Excl ())).

Definition is_RPCServer (γrpc:rpc_names) : iProp Σ :=
  inv replyTableInvN (ReplyTable_inv γrpc).

Lemma make_rpc_server E :
  ↑replyTableInvN ⊆ E →
  ⊢ |={E}=> ∃ γrpc,
    is_RPCServer γrpc ∗ (* server-side invariant *)
    RPCServer_own γrpc ∅ ∅ ∗ (* server mutex invariant *)
    [∗ set] cid ∈ fin_to_set u64, RPCClient_own γrpc cid 0.  (* SEQ counters for all possible clients *)
Proof.
Admitted.

(** Client side: allocate a new request.
Returns the request invariant and the "escrow" token to take out the reply ownership. *)
Lemma make_request (req:RPCRequest) PreCond PostCond E γrpc :
  ↑replyTableInvN ⊆ E →
  (int.nat req.(Seq)) + 1 = int.nat (word.add req.(Seq) 1) →
  is_RPCServer γrpc -∗
  RPCClient_own γrpc req.(CID) req.(Seq) -∗
  PreCond req.(Args) ={E}=∗
    RPCClient_own γrpc req.(CID) (word.add req.(Seq) 1)
    ∗ (∃ γPost, is_RPCRequest γrpc γPost PreCond PostCond req ∗ RPCRequest_token γPost).
Proof using Type*.
  iIntros (? Hsafeincr) "Hinv Hcseq_own HPreCond".
  iInv replyTableInvN as ">Hrcinv" "HNclose".
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
  iMod (inv_alloc rpcRequestInvN _ (RPCRequest_inv γrpc γPost PreCond PostCond req) with "[Hrcptsto HPreCond]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#". iLeft. iFrame.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  rewrite Hsafeincr. iFrame. iExists _; iFrame; iFrame "#".
Qed.

(** Server side: begin processing a request that is not in the reply table yet.
Returns the request precondition. *)
Lemma server_takes_request E (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ)
    (req:RPCRequest) (old_seq:u64) (γrpc:rpc_names)
    (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
  ↑rpcRequestInvN ⊆ E →
  ((map_get lastSeqM req.(CID)).1 = old_seq) →
  (int.Z req.(Seq) > int.Z old_seq)%Z →
  is_RPCRequest γrpc γP PreCond PostCond req -∗
  RPCServer_own γrpc lastSeqM lastReplyM ={E}=∗
    ▷ PreCond req.(Args)
    ∗ RPCRequestProcessing γrpc req lastSeqM lastReplyM.
Proof.
  rewrite map_get_val.
  intros ? Hlseq Hrseq.
  iIntros "HreqInv Hsown"; iNamed "Hsown".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iDestruct (big_sepS_elem_of_acc_impl req.(CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]";
    first by apply elem_of_fin_to_set.
  rewrite Hlseq.
  iDestruct "Hcases" as "[[>Hunproc Hpre]|[Hproc|Hproc]]".
  {
    iDestruct "Hunproc" as "[Hunproc_inv Hunproc]".
    iMod (fmcounter_map_update _ _ _ (int.nat req.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iMod ("HMClose" with "[Hunproc_inv]") as "_"; eauto.
    {
      iNext. iFrame "#". iRight. iLeft. iFrame.
    }
    iModIntro. iFrame "∗#".
    iApply ("Hlseq_own" with "[Hlseq_one]"); simpl.
    - rewrite lookup_insert. done.
    - iIntros "!#" (y [_ ?]). rewrite lookup_insert_ne //. eauto.
  }
  {
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.Z old_seq) with (Z.of_nat (int.nat old_seq)) in Hrseq; last by apply u64_Z_through_nat.
    replace (int.Z req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
  {
    iDestruct "Hproc" as "[#>Hlseq_lb _]".
    iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
    iExFalso; iPureIntro.
    replace (int.Z old_seq) with (Z.of_nat (int.nat old_seq)) in Hrseq; last by apply u64_Z_through_nat.
    replace (int.Z req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hlseq_lb_ineq; last by apply u64_Z_through_nat.
    lia.
  }
Qed.

(** Server side: complete processing a request and register it in the reply table.
Requires the request postcondition. *)
Lemma server_completes_request E (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ)
    (req:RPCRequest) (γrpc:rpc_names) (reply:R)
    (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γP :
  ↑replyTableInvN ⊆ E →
  ↑rpcRequestInvN ⊆ E →
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γP PreCond PostCond req -∗
  ▷ PostCond req.(Args) reply -∗
  RPCRequestProcessing γrpc req lastSeqM lastReplyM ={E}=∗
    RPCReplyReceipt γrpc req reply ∗
    RPCServer_own γrpc (<[req.(CID):=req.(Seq)]> lastSeqM) (<[req.(CID):=reply]> lastReplyM).
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
    iInv replyTableInvN as ">HNinner" "HNClose".
    iNamed "HNinner".
    iDestruct "Hproc" as "[_ Hproc]".
    iCombine "Hproc Hprocessing_ptsto" as "Hptsto".
    iDestruct (map_update _ _ (Some reply) with "Hrcctx Hptsto") as ">[Hrcctx Hrcptsto]".
    iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
    iDestruct (big_sepM_insert_2 _ _ (req.(CID), req.(Seq)) (Some reply) with "[Hreqeq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    { iNext. iExists _; iFrame; iFrame "#". }

    iDestruct (big_sepS_elem_of_acc _ _ req.(CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply elem_of_fin_to_set.
    rewrite lookup_insert /=.
    iMod (fmcounter_map_update _ _ _ (int.nat req.(Seq)) with "Hlseq_one") as "Hlseq_one"; first lia.
    iMod (fmcounter_map_get_lb with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    iSpecialize ("Hlseq_own" with "Hlseq_one").
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
    assert (Inhabited R) by exact (populate reply).
    iDestruct "Hbadptsto" as (a) "[>Hbadptsto _]".
    iDestruct (ptsto_agree_frac_value with "Hbadptsto Hprocessing_ptsto") as %[Hbad _]; done.
  }
Qed.

(** Server side: when a request [args] has a sequence number less than [lseq],
then it is stale. *)
Lemma smaller_seqno_stale_fact E (req:RPCRequest) (lseq:u64) (γrpc:rpc_names) lastSeqM lastReplyM:
  ↑replyTableInvN ⊆ E →
  lastSeqM !! req.(CID) = Some lseq →
  (int.Z req.(Seq) < int.Z lseq)%Z →
  is_RPCServer γrpc -∗
  RPCServer_own γrpc lastSeqM lastReplyM ={E}=∗
    RPCServer_own γrpc lastSeqM lastReplyM ∗
    RPCRequestStale γrpc req.
Proof.
  intros ? HlastSeqSome Hineq.
  iIntros "#Hinv [Hlseq_own #Hsepm]".
  iInv replyTableInvN as ">HNinner" "HNclose".
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
  { replace (int.Z req.(Seq)) with (Z.of_nat (int.nat req.(Seq))) in Hineq; last by apply u64_Z_through_nat.
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

(** Client side: bounding the sequence number of a stale request. *)
Lemma client_stale_seqno γrpc req seq :
  RPCRequestStale γrpc req -∗
  RPCClient_own γrpc req.(CID) seq -∗
    ⌜int.nat seq > (int.nat req.(Seq) + 1)%nat⌝%Z.
Proof.
  iIntros "Hreq Hcl".
  iDestruct (fmcounter_map_agree_strict_lb with "Hcl Hreq") as %Hlt.
  iPureIntro. done.
Qed.

(** Client side: get the postcondition out of a reply using the "escrow" token. *)
Lemma get_request_post E (req:RPCRequest) (r:R) γrpc γPost PreCond PostCond :
  ↑rpcRequestInvN ⊆ E →
  is_RPCRequest γrpc γPost PreCond PostCond req -∗
  RPCReplyReceipt γrpc req r -∗
  (own γPost (Excl ())) ={E}=∗
    ▷ (PostCond req.(Args) r).
Proof using Type*.
  assert (Inhabited R) by exact (populate r).
  iIntros (?) "#Hinv #Hptstoro HγP".
  iInv rpcRequestInvN as "HMinner" "HMClose".
  iDestruct "HMinner" as "[#>Hlseqbound [[Hbad _] | [[_ >Hbad] | HMinner]]]".
  { iDestruct (ptsto_agree_frac_value with "Hbad [$Hptstoro]") as ">[_ []]". }
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

(** Server side: lookup reply in the table, and return the appropriate receipt. *)
Lemma server_replies_to_request E `{into_val.IntoVal R} (req:RPCRequest) (γrpc:rpc_names) (reply:R)
    (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) :
  ↑replyTableInvN ⊆ E →
  (lastSeqM !! req.(CID) = Some req.(Seq)) →
  (∃ ok, map_get lastReplyM req.(CID) = (reply, ok)) →
  is_RPCServer γrpc -∗
  RPCServer_own γrpc lastSeqM lastReplyM ={E}=∗
    RPCReplyReceipt γrpc req reply ∗
    RPCServer_own γrpc (lastSeqM) (lastReplyM).
Proof.
  intros ? Hsome [ok Hreplymapget].
  iIntros "Hlinv Hsown"; iNamed "Hsown".
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
