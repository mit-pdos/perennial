From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude.
From iris.algebra Require Import gmap lib.mono_nat.
From Perennial.program_proof.lockservice Require Import fmcounter_map rpc_base.

Record durable_rpc_names := RpcNames {
  rc : gname; (* full reply history: tracks the reply for every (CID, SEQ) pair that exists, where [None] means "reply not yet determined" *)
  lseq : gname; (* latest sequence number for each client seen by server *)
  cseq : gname; (* next sequence number to be used by each client (i.e., one ahead of the latest that it used *)
  proc : gname (* token that server must have in order to start processing something *)
}.

Section rpc_durable.
Context `{!heapG Σ}.
Context {A:Type} {R:Type}.
Context `{!rpcG Σ R}.

(** The per-request invariant has 4 states.
initialized: Request created and "on its way" to the server.
processing: Request is being processed, and server has PreCond.
done: The reply was computed as is waiting for the client to take notice.
dead: The client took out ownership of the reply. *)

Implicit Types γrpc : durable_rpc_names.

Local Definition RPCRequest_durable_inv (γrpc:durable_rpc_names) (γPost γPre:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
   "#Hlseq_bound" ∷ req.(Req_CID) fm[[γrpc.(cseq)]]> int.nat req.(Req_Seq)
    ∗ ( (* Initialized, but server has not started processing *)
      "Hreply" ∷ (req.(Req_CID), req.(Req_Seq)) [[γrpc.(rc)]]↦ None ∗
               (own γrpc.(proc) (Excl ()) ∨ (* Server is processing this req *)
                own γPre (Excl ()) ∗ PreCond req.(Req_Args) (* Precondition is available *)
               ) ∨

      (* Server has finished processing; two sub-states for whether client has taken PostCond out *)
      req.(Req_CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Req_Seq)
      ∗ (∃ (last_reply:R), (req.(Req_CID), req.(Req_Seq)) [[γrpc.(rc)]]↦ro Some last_reply
        ∗ (own γPost (Excl ()) ∨ PostCond req.(Req_Args) last_reply)
      )
    ).

(** Ownership of *all* the server-side sequence number tracking tokens *)
Definition RPCServer_durable_lseq γrpc (lastSeqM:gmap u64 u64) : iProp Σ :=
  ([∗ set] cid ∈ (fin_to_set u64), cid fm[[γrpc.(lseq)]]↦ int.nat (default (U64 0) (lastSeqM !! cid)))%I.

Definition RPCServer_durable_own γrpc (lastSeqM:gmap u64 u64) lastReplyM : iProp Σ :=
    "Hlseq_own" ∷ RPCServer_durable_lseq γrpc lastSeqM
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r)
  ∗ "Hproc_own" ∷ own γrpc.(proc) (Excl ())
.

Definition RPCServer_durable_own_processing (γrpc:durable_rpc_names) (req:@RPCRequest A) lastSeqM lastReplyM : iProp Σ :=
    "Hlseq_own" ∷ RPCServer_durable_lseq γrpc lastSeqM
  ∗ ("#Hrcagree" ∷ [∗ map] cid ↦ seq ; r ∈ lastSeqM ; lastReplyM, (cid, seq) [[γrpc.(rc)]]↦ro Some r).

Local Definition ReplyTable_inv (γrpc:durable_rpc_names) : iProp Σ :=
  ∃ replyHistory:gmap (u64 * u64) (option R),
      ("Hrcctx" ∷ map_ctx γrpc.(rc) 1 replyHistory)
    ∗ ("#Hcseq_lb" ∷ [∗ map] cid_seq ↦ _ ∈ replyHistory, cid_seq.1 fm[[γrpc.(cseq)]]> int.nat cid_seq.2)
.

Definition replyTableInvN : namespace := nroot .@ "replyTableInvN".
Definition rpcRequestInvN := nroot .@ "rpcRequestInvN".

Definition is_durable_RPCRequest (γrpc:durable_rpc_names) (γPost γPre:gname) (PreCond : A -> iProp Σ) (PostCond : A -> R -> iProp Σ) (req:RPCRequest) : iProp Σ :=
  inv rpcRequestInvN (RPCRequest_durable_inv γrpc γPost γPre PreCond PostCond req).

Definition is_durable_RPCServer γrpc : iProp Σ :=
  inv replyTableInvN (ReplyTable_inv γrpc).

Global Instance RPCServer_durable_own_processing_disc γrpc (req:@RPCRequest A) lastSeqM lastReplyM : Discretizable (RPCServer_durable_own_processing γrpc req lastSeqM lastReplyM) := _.

Local Lemma new_seq_implies_unproc γrpc lastSeqM (req:@RPCRequest A) :
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  req.(Req_CID) fm[[γrpc.(lseq)]]≥ int.nat req.(Req_Seq) -∗
  RPCServer_durable_lseq γrpc lastSeqM -∗
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
  (* TODO: this integer/nat inequality reasoning is annoying.
     This works fine if the input inequality is in terms of nat's instead of Z's:
     lia.
     Might be able to change lemmas higher up the stack to use int.nat instead of int.Z.
   *)
  admit.
Admitted.

Lemma server_takes_request (req:@RPCRequest A) γrpc γPost γPre PreCond PostCond lastSeqM lastReplyM :
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_durable_RPCRequest γrpc γPost γPre PreCond PostCond req -∗
  RPCServer_durable_own γrpc lastSeqM lastReplyM
  ={⊤}=∗
  own γPre (Excl ()) ∗ ▷ PreCond req.(Req_Args) ∗
  RPCServer_durable_own_processing γrpc req lastSeqM lastReplyM.
Proof.
  intros Hrseq.
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
Lemma server_returns_request (req:@RPCRequest A) γrpc γPost γPre PreCond PostCond lastSeqM lastReplyM (old_seq:u64) :
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_durable_RPCRequest γrpc γPost γPre PreCond PostCond req -∗
  own γPre (Excl ()) -∗
  PreCond req.(Req_Args) -∗
  RPCServer_durable_own_processing γrpc req lastSeqM lastReplyM
  ={⊤}=∗
  RPCServer_durable_own γrpc lastSeqM lastReplyM.
Proof.
  intros Hrseq.
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

(* TODO: move this to the top *)
Definition RPCReplyReceipt γrpc (req:@RPCRequest A) (r:R) : iProp Σ :=
  (req.(Req_CID), req.(Req_Seq)) [[γrpc.(rc)]]↦ro Some r
.

(* TODO: I think this SP will be annoying *)
Lemma server_executes_durable_request' (req:@RPCRequest A) reply γrpc γPost γPre PreCond PostCond lastSeqM lastReplyM ctx ctx' SP:
  (* TODO: get rid of this requirement by putting γPre in the postcondition case *)
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_durable_RPCRequest γrpc γPost γPre PreCond PostCond req -∗
  is_durable_RPCServer γrpc -∗
  RPCServer_durable_own_processing γrpc req lastSeqM lastReplyM -∗
  own γPre (Excl()) -∗
  SP -∗
  (▷ SP -∗ ctx ==∗ PostCond req.(Req_Args) reply ∗ ctx') -∗
  ctx ={⊤}=∗
  (RPCReplyReceipt γrpc req reply ∗
  RPCServer_durable_own γrpc (<[req.(Req_CID):=req.(Req_Seq)]> lastSeqM) (<[req.(Req_CID):=reply]> lastReplyM) ∗
  ctx').
Proof.
  intros Hrseq.
  iIntros "#HreqInv #HsrvInv Hsrpc_proc HγPre HP Hfupd Hctx".
  iNamed "Hsrpc_proc".
  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iDestruct "Hcases" as "[[>Hrcptsto [>Hproc_tok|[>HγPre2 _]]]|[>#Hlseq_lb _]]".
  {
    iMod ("Hfupd" with "HP Hctx") as "[Hpost Hctx']".
    
    iInv replyTableInvN as ">HNinner" "HNClose".
    iNamed "HNinner".

    iDestruct (map_update _ _ (Some reply) with "Hrcctx Hrcptsto") as ">[Hrcctx Hrcptsto]".
    iDestruct (map_freeze with "Hrcctx Hrcptsto") as ">[Hrcctx #Hrcptsoro]".
    iDestruct (big_sepM_insert_2 _ _ (req.(Req_CID), req.(Req_Seq)) (Some reply) with "[Hreqeq_lb] Hcseq_lb") as "Hcseq_lb2"; eauto.
    iMod ("HNClose" with "[Hrcctx Hcseq_lb2]") as "_".
    {
      iNext. iExists _; iFrame "# ∗".
    }

    iDestruct (big_sepS_elem_of_acc_impl req.(Req_CID) with "Hlseq_own") as "[Hlseq_one Hlseq_own]";
      first by apply elem_of_fin_to_set.
    iMod (fmcounter_map_update (int.nat req.(Req_Seq)) with "Hlseq_one") as "[Hlseq_one #Hlseq_new_lb]".
    { rewrite map_get_val in Hrseq. (* TODO: more annoying nat/int reasoning. *) admit. }

    iMod ("HMClose" with "[Hpost]") as "_".
    { iNext. iFrame "#". iRight. iExists _; iFrame "#". by iRight. }
    iDestruct (big_sepM2_insert_2 _ lastSeqM lastReplyM req.(Req_CID) req.(Req_Seq) reply with "[Hreqeq_lb] Hrcagree") as "Hrcagree2"; eauto.
    iModIntro.
    iFrame "∗#".
    iApply ("Hlseq_own" with "[Hlseq_one]"); simpl.
    - rewrite lookup_insert. done.
    - iIntros "!#" (y [_ ?]). rewrite lookup_insert_ne //. eauto.
  }
  { by iDestruct (own_valid_2 with "HγPre HγPre2") as %Hbad. }
  { by iExFalso; iApply (new_seq_implies_unproc with "Hlseq_lb Hlseq_own"). }
Admitted.

End rpc_durable.
