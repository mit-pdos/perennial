From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.program_proof Require Import disk_prelude.
From iris.algebra Require Import gmap lib.mono_nat.
From Perennial.base_logic Require Export lib.ghost_map.
From Perennial.program_proof.lockservice Require Import fmcounter_map.

(** RPC layer ghost names. *)
Record rpc_names := RpcNames {
  rc : gname; (* full reply history: tracks the reply for every (CID, SEQ) pair that exists, where [None] means "reply not yet determined" *)
  lseq : gname; (* latest sequence number for each client seen by server *)
  cseq : gname; (* next sequence number to be used by each client (i.e., one ahead of the latest that it used *)
  proc : gname (* token that server must have in order to start processing a request *)
}.

Record rpc_request_names := RpcRequestNames {
  pre : gname; (* token that a server holds while using the precondition of a request; gets exchanged with the server's proc token *)
  post : gname (* token that a client can exchanged for the post condition of a request, if they have a reply receipt *)
}.

(** Colelcting the CMRAs we need. *)
Class rpcG Σ (R : Type) := RpcG {
  rpc_fmcounterG :> fmcounter_mapG Σ;
  rpc_escrowG :> inG Σ (exclR unitO);
  rpc_mapG :> ghost_mapG Σ (u64*u64) (option R);
}.
(* FIXME: add subΣ instance. *)

Section rpc.
Context `{ffi_sem: ext_semantics} `{!ffi_interp ffi} `{!heapG Σ}.
Context {ext_ty: ext_types ext}.
Context  {R:Type}.
Context `{!rpcG Σ R}.

(* identifier for a rpc request *)
Record RPCRequestID :=
{
  Req_CID : u64 ;
  Req_Seq : u64 ;
}.

Record RPCReply :=
{
  Rep_Stale : bool ;
  Rep_Ret : R ;
}.

Definition RPCClient_own_ghost (γrpc:rpc_names) (cid cseqno:u64) : iProp Σ :=
  "Hcseq_own" ∷ (cid fm[[γrpc.(cseq)]]↦ int.nat cseqno)
.

Implicit Types γrpc : rpc_names.
Implicit Types γreq : rpc_request_names.

(** Ownership of *all* the server-side sequence number tracking tokens *)
Definition RPCServer_lseq γrpc (lastSeqM:gmap u64 u64) : iProp Σ :=
  ([∗ set] cid ∈ (fin_to_set u64), cid fm[[γrpc.(lseq)]]↦ int.nat (default (U64 0) (lastSeqM !! cid)))%I.

Definition RPCServer_own_ghost γrpc (lastSeqM:gmap u64 u64) lastReplyM : iProp Σ :=
    "Hlseq_own" ∷ RPCServer_lseq γrpc lastSeqM
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) ↪[γrpc.(rc)]□ Some r)
  ∗ "Hproc_own" ∷ own γrpc.(proc) (Excl ())
.

Definition RPCServer_own_processing γrpc (req:RPCRequestID) lastSeqM lastReplyM : iProp Σ :=
    "Hlseq_own" ∷ RPCServer_lseq γrpc lastSeqM
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) ↪[γrpc.(rc)]□ Some r).

Definition RPCRequest_token γreq : iProp Σ :=
  (own γreq.(post) (Excl ())).

Definition RPCReplyReceipt γrpc (req:RPCRequestID) (r:R) : iProp Σ :=
  (req.(Req_CID), req.(Req_Seq)) ↪[γrpc.(rc)]□ Some r
.

Definition RPCRequestStale γrpc (req:RPCRequestID) : iProp Σ :=
  (req.(Req_CID) fm[[γrpc.(cseq)]]> ((int.nat req.(Req_Seq)) + 1))
.

(** The per-request invariant has 4 states.
initialized: Request created and "on its way" to the server.
processing: Request is being processed, and server has PreCond.
done: The reply was computed as is waiting for the client to take notice.
dead: The client took out ownership of the reply. *)

Local Definition RPCRequest_inv γrpc γreq (PreCond : iProp Σ) (PostCond : R -> iProp Σ) (req:RPCRequestID) : iProp Σ :=
   "#Hlseq_bound" ∷ req.(Req_CID) fm[[γrpc.(cseq)]]> int.nat req.(Req_Seq) ∗
    ( (* Initialized, but server has not started processing *)
      "Hreply" ∷ (req.(Req_CID), req.(Req_Seq)) ↪[γrpc.(rc)] None ∗
               (own γrpc.(proc) (Excl ()) ∨ (* Server is processing this req *)
                own γreq.(pre) (Excl ()) ∗ PreCond (* Precondition is available *)
               ) ∨

      (* Server has finished processing; two sub-states for whether client has taken PostCond out *)
      req.(Req_CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Req_Seq) ∗
        (own γreq.(post) (Excl ()) ∨
        (∃ (last_reply:R), (req.(Req_CID), req.(Req_Seq)) ↪[γrpc.(rc)]□ Some last_reply ∗
          (PostCond last_reply))
      )
    ).

Local Definition ReplyTable_inv γrpc: iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option R),
      ("Hrcctx" ∷ ghost_map_auth γrpc.(rc) 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γrpc.(cseq)]]> int.nat cid_seq.2)
.

Definition replyTableInvN : namespace := nroot .@ "replyTableInvN".
Definition rpcRequestInvN req := nroot .@ "rpcRequestInvN" .@ (req.(Req_Seq)).

Definition is_RPCRequest γrpc γreq (PreCond : iProp Σ) (PostCond : R -> iProp Σ) (req:RPCRequestID) : iProp Σ :=
  inv (rpcRequestInvN req) (RPCRequest_inv γrpc γreq PreCond PostCond req).

Definition is_RPCServer γrpc : iProp Σ :=
  inv replyTableInvN (ReplyTable_inv γrpc).

Global Instance RPCServer_durable_own_processing_disc γrpc (req:RPCRequestID) lastSeqM lastReplyM : Discretizable (RPCServer_own_processing γrpc req lastSeqM lastReplyM) := _.

(* Allocate ghost state and invariant for reply table *)
Lemma make_rpc_server E :
  ↑replyTableInvN ⊆ E →
  ⊢ |={E}=> ∃ γrpc,
    is_RPCServer γrpc ∗ (* server-side invariant *)
    RPCServer_own_ghost γrpc ∅ ∅ ∗ (* server mutex invariant *)
    [∗ set] cid ∈ fin_to_set u64, RPCClient_own_ghost γrpc cid 1. (* SEQ counters for all possible clients *)
Proof.
  iIntros (?).
  iMod fmcounter_map_alloc as (γcseq) "Hcseq".
  iMod fmcounter_map_alloc as (γlseq) "Hlseq".
  iMod (ghost_map_alloc (∅ : gmap (u64*u64) (option R))) as (γrc) "[Hrc _]".
  iMod (own_alloc (Excl ())) as (γproc) "Hγproc"; first done.
  pose (γrpc := RpcNames γrc γlseq γcseq γproc).
  iExists γrpc.
  rewrite /is_RPCServer /RPCServer_own_ghost /RPCClient_own_ghost /=.
  iMod (inv_alloc _ _ (ReplyTable_inv γrpc) with "[Hrc]") as "$".
  { iExists ∅. iFrame. iNext. iApply big_sepM_empty. done. }
  iFrame "Hcseq". iFrame. iSplitL; last by iApply big_sepM2_empty.
  rewrite /RPCServer_lseq /=. iApply (big_sepS_impl with "Hlseq").
  iIntros "!> !#" (cid _). rewrite lookup_empty. eauto.
Qed.

(** Client side: allocate a new request.
Returns the request invariant and the "escrow" token to take out the reply ownership. *)
Lemma make_request (req:RPCRequestID) PreCond PostCond E γrpc :
  ↑replyTableInvN ⊆ E →
  ((int.nat req.(Req_Seq)) + 1)%nat = int.nat (word.add req.(Req_Seq) 1) →
  is_RPCServer γrpc -∗
  RPCClient_own_ghost γrpc req.(Req_CID) req.(Req_Seq) -∗
  ▷ PreCond ={E}=∗
    RPCClient_own_ghost γrpc req.(Req_CID) (word.add req.(Req_Seq) 1)
    ∗ (∃ γreq, is_RPCRequest γrpc γreq PreCond PostCond req ∗ RPCRequest_token γreq).
Proof using Type*.
  iIntros (? Hsafeincr) "Hinv Hcseq_own HPreCond".
  iInv replyTableInvN as ">Hrcinv" "HNclose".
  iNamed "Hrcinv".
  destruct (replyHistory !! (req.(Req_CID), req.(Req_Seq))) eqn:Hrh.
  {
    iExFalso.
    iDestruct (big_sepM_delete with "Hcseq_lb") as "[Hbad _]"; first eauto.
    simpl.
    iDestruct (fmcounter_map_agree_strict_lb with "Hcseq_own Hbad") as %Hbad.
    iPureIntro. simpl in Hbad.
    lia.
  }
  iMod (ghost_map_insert (req.(Req_CID), req.(Req_Seq)) None with "Hrcctx") as "[Hrcctx Hrcptsto]"; first done.
  iMod (own_alloc (Excl ())) as (γpost) "Hγpost"; first done.
  iMod (own_alloc (Excl ())) as (γpre) "Hγpre"; first done.
  pose (γreq := RpcRequestNames γpre γpost).
  iMod (fmcounter_map_update (int.nat req.(Req_Seq) + 1) with "Hcseq_own") as "[Hcseq_own #Hcseq_lb_one]".
  { simpl. lia. }
  iDestruct (big_sepM_insert _ _ _ None with "[$Hcseq_lb Hcseq_lb_one]") as "#Hcseq_lb2"; eauto.
  iMod (inv_alloc (rpcRequestInvN req) _ (RPCRequest_inv γrpc γreq PreCond PostCond req) with "[Hrcptsto HPreCond Hγpre]") as "#Hreqinv_init".
  {
    iNext. iFrame; iFrame "#". iLeft. iFrame. iRight. iFrame.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  { iNext. iExists _. iFrame; iFrame "#". }
  iModIntro.
  rewrite Hsafeincr. iFrame. iExists _; iFrame "∗#". iFrame.
Qed.

Local Lemma new_seq_implies_unproc γrpc lastSeqM (req:RPCRequestID) :
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  req.(Req_CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Req_Seq) -∗
  RPCServer_lseq γrpc lastSeqM -∗
  False.
Proof.
  rewrite map_get_val.
  intros Hrseq.
  iIntros "Hlseq_lb Hlseq_own".
  iDestruct (big_sepS_elem_of_acc_impl req.(Req_CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]";
    first by apply elem_of_fin_to_set.
  iDestruct (fmcounter_map_agree_lb with "Hlseq_one Hlseq_lb") as %Hlseq_lb_ineq.
  iPureIntro.
  set cur_seq:=(default IntoVal_def (lastSeqM !! req.(Req_CID))) in Hrseq Hlseq_lb_ineq.
  word.
Qed.

Lemma server_takes_request E (req:RPCRequestID) γrpc γreq PreCond PostCond lastSeqM lastReplyM :
  ↑(rpcRequestInvN req) ⊆ E →
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  RPCServer_own_ghost γrpc lastSeqM lastReplyM
  ={E}=∗
  own γreq.(pre) (Excl ()) ∗ ▷ PreCond ∗
  RPCServer_own_processing γrpc req lastSeqM lastReplyM.
Proof.
  intros ? Hrseq.
  iIntros "HreqInv Hsown"; iNamed "Hsown".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".

  iDestruct "Hcases" as "[[>Hunproc Hpre]|[#>Hlseq_lb _]]".
  {
    iDestruct "Hpre" as "[>Hbad|[>HγP Hpre]]".
    - (* impossible case: precond was taken out previously, and proc token is in the invariant *)
        by iDestruct (own_valid_2 with "Hbad Hproc_own") as %Hbad.
    - (* case: precond available *)
    iMod ("HMClose" with "[Hunproc Hproc_own]") as "_".
    {
      iNext. iFrame "#".
      iLeft. iFrame.
    }
    iModIntro. iFrame.
    iFrame "# ∗".
  }
  { (* impossible case: reply for request has already been set *)
    by iExFalso; iApply (new_seq_implies_unproc with "Hlseq_lb Hlseq_own").
  }
Qed.

(* Opposite of above *)
Lemma server_returns_request E (req:RPCRequestID) γrpc γreq PreCond PostCond lastSeqM lastReplyM :
  ↑(rpcRequestInvN req) ⊆ E →
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  own γreq.(pre) (Excl ()) -∗
  PreCond -∗
  RPCServer_own_processing γrpc req lastSeqM lastReplyM
  ={E}=∗
  RPCServer_own_ghost γrpc lastSeqM lastReplyM.
Proof.
  intros ? Hrseq.
  iIntros "HreqInv HγPre Hpre Hsrpc_proc".
  iNamed "Hsrpc_proc".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".

  iDestruct "Hcases" as "[[>Hunproc Hpre2]|[#>Hlseq_lb _]]".
  {
    iDestruct "Hpre2" as "[>Hproc_tok|[>HγPre2 _]]".
    - iMod ("HMClose" with "[HγPre Hpre Hunproc]") as "_"; last by [iModIntro; iFrame].
      iNext. iFrame "#". iLeft. iFrame "#∗". iRight. iFrame.
    - by iDestruct (own_valid_2 with "HγPre HγPre2") as %Hbad.
  }
  {
    by iExFalso; iApply (new_seq_implies_unproc with "Hlseq_lb Hlseq_own").
  }
Qed.

(** Server side: complete processing a request and register it in the reply table.
Requires the request postcondition. *)
Lemma server_completes_request E (PreCond : iProp Σ) (PostCond : R -> iProp Σ)
    (req:RPCRequestID) (γrpc:rpc_names) (reply:R)
    (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) γreq :
  ↑replyTableInvN ⊆ E →
  (↑rpcRequestInvN req ⊆ E) →
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  own γreq.(pre) (Excl ()) -∗
  ▷ PostCond reply -∗
  RPCServer_own_processing γrpc req lastSeqM lastReplyM ={E}=∗
    RPCReplyReceipt γrpc req reply ∗
    RPCServer_own_ghost γrpc (<[req.(Req_CID):=req.(Req_Seq)]> lastSeqM) (<[req.(Req_CID):=reply]> lastReplyM).
Proof using Type*.
  rewrite map_get_val.
  intros.
  iIntros "Hlinv HreqInv Hγpre Hpost Hprocessing"; iNamed "Hprocessing".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iDestruct "Hcases" as "[[>Hunproc [>Hproc|[>Hγpre2 _]]]|[#>Hlseq_lb Hproc]]".
  2: {
    iDestruct (own_valid_2 with "Hγpre Hγpre2") as %?; contradiction.
  }
  {
    iInv replyTableInvN as ">HNinner" "HNClose".
    iNamed "HNinner".
    iMod (ghost_map_update (Some reply) with "Hrcctx Hunproc") as "[Hrcctx Hrcptsto]".
    iMod (ghost_map_elem_persist with "Hrcptsto") as "#Hrcptsoro".
    iDestruct (big_sepM_insert_2 _ _ (req.(Req_CID), req.(Req_Seq)) (Some reply) with "[Hreqeq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    { iNext. iExists _; iFrame; iFrame "#". }

    iDestruct (big_sepS_elem_of_acc_impl req.(Req_CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]"; first by apply elem_of_fin_to_set.
    iMod (fmcounter_map_update (int.nat req.(Req_Seq)) with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    {
      (* Set Printing All*)
      (* Need to unfold Map.t to get map lookups to match *)
      unfold Map.t in H1.
      simpl in H1.
      rewrite -u64_Z_through_nat in H1.
      replace (int.Z req.(Req_Seq)%Z) with (int.nat req.(Req_Seq):Z) in H1; last first.
      { rewrite u64_Z_through_nat. done. }
      apply Nat2Z.inj_lt in H1.
      lia.
    }
    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iRight. iExists _; iFrame "#∗". }
    iModIntro.

    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM req.(Req_CID) req.(Req_Seq) reply with "[Hreqeq_lb] Hrcagree") as "Hrcagree2"; eauto.
    iFrame "∗#".
    iApply ("Hlseq_own" with "[] [Hlseq_one]"); simpl.
    - iIntros "!#" (y _ ?). rewrite lookup_insert_ne //. eauto.
    - rewrite lookup_insert. done.
  }
  { (* One-shot update of γrc already happened; this is impossible *)
    by iExFalso; iApply (new_seq_implies_unproc with "Hlseq_lb Hlseq_own").
  }
Qed.

(** Server side: when a request [args] has a sequence number less than [lseq],
then it is stale. *)
Lemma smaller_seqno_stale_fact E (req:RPCRequestID) (lseq:u64) (γrpc:rpc_names) lastSeqM lastReplyM:
  ↑replyTableInvN ⊆ E →
  lastSeqM !! req.(Req_CID) = Some lseq →
  (int.Z req.(Req_Seq) < int.Z lseq)%Z →
  is_RPCServer γrpc -∗
  RPCServer_own_ghost γrpc lastSeqM lastReplyM ={E}=∗
    RPCServer_own_ghost γrpc lastSeqM lastReplyM ∗
    RPCRequestStale γrpc req.
Proof.
  intros ? HlastSeqSome Hineq.
  iIntros "#Hinv (Hlseq_own & #Hsepm & Hproc)".
  iInv replyTableInvN as ">HNinner" "HNclose".
  iNamed "HNinner".
  iDestruct (big_sepM2_dom with "Hsepm") as %Hdomeq.
  assert (is_Some (lastReplyM !! req.(Req_CID))) as HlastReplyIn.
  { apply elem_of_dom. assert (is_Some (lastSeqM !! req.(Req_CID))) as HlastSeqSome2 by eauto. apply elem_of_dom in HlastSeqSome2.
    rewrite <- Hdomeq. done. }
  destruct HlastReplyIn as [r HlastReplyIn].
  iDestruct (big_sepM2_delete _ _ _ _ lseq r with "Hsepm") as "[Hptstoro _]"; eauto.
  iDestruct (ghost_map_lookup with "Hrcctx Hptstoro") as %HinReplyHistory.
  iDestruct (big_sepM_delete with "Hcseq_lb") as "[Hcseq_lb_one _] /="; eauto.
  iDestruct (fmcounter_map_mono_lb (int.nat req.(Req_Seq) + 2) with "Hcseq_lb_one") as "#HStaleFact".
  { replace (int.Z req.(Req_Seq)) with (Z.of_nat (int.nat req.(Req_Seq))) in Hineq; last by apply u64_Z_through_nat.
    simpl.
    lia.
  }
  iMod ("HNclose" with "[Hrcctx]") as "_".
  {
    iNext. iExists _; iFrame; iFrame "#".
  }
  iModIntro. replace (int.nat req.(Req_Seq) + 2)%nat with (int.nat req.(Req_Seq) + 1 + 1)%nat by lia.
  iFrame; iFrame "#".
Qed.

(** Client side: bounding the sequence number of a stale request. *)
Lemma client_stale_seqno γrpc req seq :
  RPCRequestStale γrpc req -∗
  RPCClient_own_ghost γrpc req.(Req_CID) seq -∗
    ⌜int.nat seq > (int.nat req.(Req_Seq) + 1)%nat⌝%Z.
Proof.
  iIntros "Hreq Hcl".
  iDestruct (fmcounter_map_agree_strict_lb with "Hcl Hreq") as %Hlt.
  iPureIntro. lia.
Qed.

(** Client side: get the postcondition out of a reply using the "escrow" token. *)
Lemma get_request_post E (req:RPCRequestID) (r:R) γrpc γreq PreCond PostCond :
  ↑rpcRequestInvN req ⊆ E →
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  RPCReplyReceipt γrpc req r -∗
  (RPCRequest_token γreq) ={E}=∗
    ▷ (PostCond r).
Proof using Type*.
  assert (Inhabited R) by exact (populate r).
  iIntros (?) "#Hinv #Hptstoro HγP".
  iInv "Hinv" as "HMinner" "HMClose".
  iDestruct "HMinner" as "[#>Hlseqbound [[>Hbad _] | [#Hlseq_lb HMinner]]]".
  { iDestruct (ghost_map_elem_valid_2 with "Hbad [$Hptstoro]") as "[%%]". done. }
  iDestruct "HMinner" as "[>Hγpost|Hreply_post]".
  { by iDestruct (own_valid_2 with "HγP Hγpost") as %Hbad. }
  iDestruct "Hreply_post" as (last_reply) "[#Hreply Hpost]".
  iMod ("HMClose" with "[HγP]") as "_".
  { iNext. iFrame "#". iRight. iLeft. done. }
  iModIntro. iModIntro.
  iDestruct (ghost_map_elem_agree with "Hreply Hptstoro") as %Heq.
  by injection Heq as ->.
Qed.

(** Server side: lookup reply in the table, and return the appropriate receipt. *)
Lemma server_replies_to_request E (req:RPCRequestID) (γrpc:rpc_names) (reply:R)
    (lastSeqM:gmap u64 u64) (lastReplyM:gmap u64 R) :
  ↑replyTableInvN ⊆ E →
  (lastSeqM !! req.(Req_CID) = Some req.(Req_Seq)) →
  (∃ def, default def (lastReplyM !! req.(Req_CID)) = reply) →
  is_RPCServer γrpc -∗
  RPCServer_own_ghost γrpc lastSeqM lastReplyM ={E}=∗
    RPCReplyReceipt γrpc req reply ∗
    RPCServer_own_ghost γrpc (lastSeqM) (lastReplyM).
Proof.
  intros ? Hsome [def Hreplymapget].
  iIntros "Hlinv Hsown"; iNamed "Hsown".
  destruct (lastReplyM !! req.(Req_CID)) as [] eqn:X; last first.
  { iDestruct (big_sepM2_lookup_1 _ _ _ req.(Req_CID) with "Hrcagree") as (x Hmap) "?"; eauto.
    exfalso. naive_solver. }
  assert (r = reply) as -> by naive_solver.
  iDestruct (big_sepM2_delete with "Hrcagree") as "[#Hrcptsto _]"; eauto.
  iModIntro.
  iFrame "#"; iFrame.
Qed.

(* TODO: I think this SP will be annoying *)
Lemma server_executes_durable_request (req:RPCRequestID) reply γrpc γreq PreCond PostCond lastSeqM lastReplyM ctx ctx' SP:
  (* TODO: get rid of this requirement by putting γPre in the postcondition case *)
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  is_RPCServer γrpc -∗
  RPCServer_own_processing γrpc req lastSeqM lastReplyM -∗
  own γreq.(pre) (Excl()) -∗
  (SP) -∗ (* strengthened precond *)
  (SP -∗ own γrpc.(proc) (Excl ()) -∗ req.(Req_CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Req_Seq) -∗ ctx
      ={⊤ ∖ ↑rpcRequestInvN req}=∗ PostCond reply ∗ own γrpc.(proc) (Excl ()) ∗ ctx') -∗
  ctx ={⊤}=∗
  (RPCReplyReceipt γrpc req reply ∗
  RPCServer_own_ghost γrpc (<[req.(Req_CID):=req.(Req_Seq)]> lastSeqM) (<[req.(Req_CID):=reply]> lastReplyM) ∗
  ctx').
Proof.
  (* XXX: without [V:=u64], u64 gets unfolded here, which forces us to later unfold u64 more so we can match against Hrseq.*)
  rewrite (map_get_val (V:=u64)).
  intros Hrseq.
  iIntros "#HreqInv #HsrvInv Hsrpc_proc HγPre HP Hfupd Hctx".
  iNamed "Hsrpc_proc".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iDestruct "Hcases" as "[[>Hrcptsto [>Hproc_tok|[>HγPre2 _]]]|[>#Hlseq_lb _]]".
  {

    iInv replyTableInvN as ">HNinner" "HNClose".
    iNamed "HNinner".

    iMod (ghost_map_update (Some reply) with "Hrcctx Hrcptsto") as "[Hrcctx Hrcptsto]".
    iMod (ghost_map_elem_persist with "Hrcptsto") as "#Hrcptsoro".
    iDestruct (big_sepM_insert_2 _ _ (req.(Req_CID), req.(Req_Seq)) (Some reply) with "[Hreqeq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    {
      iNext. iExists _; iFrame "# ∗".
    }

    iDestruct (big_sepS_elem_of_acc_impl req.(Req_CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]";
      first by apply elem_of_fin_to_set.
    iMod (fmcounter_map_update (int.nat req.(Req_Seq)) with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    {
      simpl in Hrseq.
      replace (int.Z req.(Req_Seq)%Z) with (int.nat req.(Req_Seq):Z) in Hrseq; last first.
      { rewrite u64_Z_through_nat. done. }
      rewrite -u64_Z_through_nat in Hrseq.
      unfold Map.t in Hrseq.
      apply Nat2Z.inj_lt in Hrseq.
      lia.
    }

    (* COMMIT POINT *)
    iMod ("Hfupd" with "HP Hproc_tok Hlseq_new_lb Hctx") as "(Hpost & Hγproc & Hctx')".

    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iRight. iExists _; iFrame "#∗". }
    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM req.(Req_CID) req.(Req_Seq) reply with "[Hreqeq_lb] Hrcagree") as "Hrcagree2"; eauto.
    iModIntro.
    iFrame "∗#".
    iApply ("Hlseq_own" with "[] [Hlseq_one]"); simpl.
    - iIntros "!#" (y _ ?). rewrite lookup_insert_ne //. eauto.
    - rewrite lookup_insert. done.
  }
  { by iDestruct (own_valid_2 with "HγPre HγPre2") as %Hbad. }
  { by iExFalso; iApply (new_seq_implies_unproc with "Hlseq_lb Hlseq_own"). }
Qed.

End rpc.
