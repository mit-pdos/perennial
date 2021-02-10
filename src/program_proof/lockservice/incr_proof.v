From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof rpc_durable_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section rpc_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.

Definition rpcReqInvUpToN (seqno:u64) : coPset.
Admitted.
(* big union *)

Lemma rpcReqInvUpToN_prop cid seq :
 ∀ seq', int.nat seq' < int.nat seq → (↑rpcRequestInvN {|Req_CID:=cid; Req_Seq:=seq' |}) ⊆ rpcReqInvUpToN seq.
Admitted.

Lemma rpcReqInvUpToN_prop_2 cid seq :
 ∀ seq', int.nat seq' ≥ int.nat seq → ↑rpcRequestInvN {|Req_CID:=cid; Req_Seq:=seq' |} ## rpcReqInvUpToN seq.
Admitted.

(* Need this fupd to be OK to fire with any sequence number larger than the *)
Definition rpc_atomic_pre_fupd γrpc (cid seq:u64) R : iProp Σ :=
  (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ R)%I.

(* This gives the rpc_atomic_pre_fupd for any sequence number that the client can take on
   This is the precondition for ck.MakeRequest(args), where ck has the given cid *)
Definition rpc_atomic_pre γrpc cid R : iProp Σ :=
    <bdisc> (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗
    cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
   (laterable.make_laterable (rpc_atomic_pre_fupd γrpc cid seq R))).

(* TODO: Want a quiesce_fupd that gives a user-chosen resource so long as one provides a proof that (PreCond ∨ PostCond ={⊤}=∗ user-chosen-resource) *)
(* E.g. if we want to do a new Put() after giving up on a Get(), we should be able to quiesce the Get() and  *)

Definition own_rpcclient (cl_ptr:loc) (γrpc:rpc_names) (cid:u64) : iProp Σ
  :=
    ∃ (cseqno:u64),
      "%" ∷ ⌜int.nat cseqno > 0⌝
    ∗ "Hcid" ∷ cl_ptr ↦[RPCClient.S :: "cid"] #cid
    ∗ "Hseq" ∷ cl_ptr ↦[RPCClient.S :: "seq"] #cseqno
    ∗ "Hcrpc" ∷ RPCClient_own γrpc cid cseqno
.

Theorem wpc_forBreak_cond' (P: iProp Σ) stk k E (cond body: goose_lang.val) (Φ : goose_lang.val → iProp Σ) (Φc: iProp Σ) :
  P -∗
  (P -∗ <disc> Φc) -∗
  □ (P -∗
      WPC if: cond #() then body #() else #false @ stk; k; E
      {{ v, ⌜v = #true⌝ ∗ P ∨ ⌜v = #false⌝ ∗ (Φ #() ∧ <disc> Φc) }} {{ Φc }} ) -∗
  WPC (for: cond; (λ: <>, Skip)%V := body) @ stk; k ; E {{ Φ }} {{ Φc }}.
Proof.
  iIntros "HP HΦc #Hbody".
  rewrite /For.
  iCache with "HP HΦc".
  { by iApply "HΦc". }
  wpc_pures.
  iLöb as "IH".
  wpc_bind_seq.
  iDestruct ("Hbody" with "HP") as "Hbody1".
  iApply (wpc_strong_mono with "Hbody1"); try auto.
  iSplit; last first.
  {
    iModIntro. iIntros.
    by iModIntro.
  }
  iIntros (v) "H".
  iModIntro.
  iDestruct "H" as "[[% H]|[% H]]"; subst.
  - iCache with "HΦc H".
    { iSpecialize ("HΦc" with "H"). done. }
    wpc_pures.
    wpc_pures.
    iApply ("IH" with "[$] [$]").
  - iCache with "H".
    { by iRight in "H". }
    wpc_pures.
    wpc_pures.
    by iLeft in "H".
Qed.

Lemma rpc_atomic_pre_fupd_mono_strong γrpc cid seq P Q:
  (P -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq -∗
     own γrpc.(proc) (Excl ())={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ Q) -∗
  rpc_atomic_pre_fupd γrpc cid seq P -∗
  rpc_atomic_pre_fupd γrpc cid seq Q.
Proof.
  iIntros "HPQ HfupdP Hγproc #Hlb".
  iMod ("HfupdP" with "Hγproc Hlb") as "[Hγproc HP]".
  iSpecialize ("HPQ" with "HP Hlb Hγproc").
  iMod "HPQ".
  iFrame.
  by iModIntro.
Qed.

Lemma rpc_atomic_pre_mono_strong cid γrpc P Q :
  □(∀ seq, cid fm[[γrpc.(lseq)]]≥ int.nat seq → P -∗ own γrpc.(proc) (Excl ())={rpcReqInvUpToN seq}=∗ own γrpc.(proc) (Excl ()) ∗ Q) -∗
  rpc_atomic_pre γrpc cid P -∗
  rpc_atomic_pre γrpc cid Q.
Proof.
  iIntros "#HPQ HatomicP".
  iModIntro.
  iIntros (seq) "Hcown".
  iMod ("HatomicP" $! seq with "Hcown") as "[Hcown HatomicP]".
  iFrame.
  unfold laterable.make_laterable.
  iDestruct "HatomicP" as (R) "[HR #HatomicP]".
  iExists (R). iFrame.
  iModIntro.
  iModIntro.
  iIntros "HR". iSpecialize ("HatomicP" with "HR").
  iApply (rpc_atomic_pre_fupd_mono_strong with "[HPQ] HatomicP").
  iIntros "HP #Hlb Hγproc".
  iDestruct ("HPQ" $! seq with "Hlb HP Hγproc") as "$".
Qed.

(*
Lemma rpc_atomic_pre_fupd_mono γrpc cid seq P Q:
  (P -∗ Q) -∗
  rpc_atomic_pre_fupd γrpc cid seq P -∗
  rpc_atomic_pre_fupd γrpc cid seq Q.
Proof.
  iIntros "HPQ".
  iApply rpc_atomic_pre_fupd_mono_strong.
  iIntros "HP _ $".
  by iApply "HPQ".
Qed.

Lemma rpc_atomic_pre_mono cid γrpc P Q :
  <bdisc>(P -∗ Q) -∗
  rpc_atomic_pre γrpc cid P -∗
  rpc_atomic_pre γrpc cid Q.
Proof.
  iIntros "HPQ HatomicP".
  iModIntro.
  iIntros (seq) "Hcown".
  iMod ("HatomicP" $! seq with "Hcown") as "[Hcown HatomicP]".
  iFrame.
  iApply (rpc_atomic_pre_fupd_mono with "HPQ HatomicP").
Qed.
*)

Definition quiesce_fupd γrpc cid seqno PreCond PostCond : iProp Σ :=
  laterable.make_laterable (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))%I.

Definition quiesceable_pre γrpc cid PreCond PostCond : iProp Σ :=
  rpc_atomic_pre γrpc cid (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret)%I.

Global Instance quiesceable_pre_disc γrpc cid PreCond PostCond : (Discretizable
       (quiesceable_pre γrpc cid PreCond PostCond)).
Proof.
  rewrite /Discretizable.
  by rewrite -own_discrete_idemp.
Defined.

Lemma quiesce_request (req:RPCRequestID) γrpc γreq (PreCond:iProp Σ) PostCond  :
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  (RPCRequest_token γreq) -∗
  quiesceable_pre γrpc req.(Req_CID) PreCond PostCond.
Proof.
    iIntros "#Hsrpc #His_req Hγpost".
    iFrame "#∗".

    iModIntro.

    iIntros (new_seq) "Hcown".
    iInv "His_req" as "[>#Hcseq_lb_strict HN]" "HNClose".
    iMod ("HNClose" with "[$Hcseq_lb_strict $HN]") as "_".

    iDestruct (fmcounter_map_agree_lb with "Hcown Hcseq_lb_strict") as %Hnew_seq.
    iFrame.
    iModIntro.
    iExists (RPCRequest_token γreq).
    iFrame.
    iModIntro.
    iIntros ">Hγpost".

    iIntros "Hγproc #Hlseq_lb".
    iInv "His_req" as "HN" "HNClose".
    { apply (rpcReqInvUpToN_prop req.(Req_CID)). destruct req. simpl in *. word. }
    iDestruct "HN" as "[#>_ [HN|HN]]"; simpl. (* Is cseq_lb_strict relevant for this? *)
    {
      iDestruct "HN" as "[_ [>Hbad|HN]]".
      { iDestruct (own_valid_2 with "Hbad Hγproc") as %?; contradiction. }

      iMod ("HNClose" with "[Hγpost]") as "_".
      { iNext. iFrame "Hcseq_lb_strict". iRight. iFrame.
        iDestruct (fmcounter_map_mono_lb (int.nat req.(Req_Seq)) with "Hlseq_lb") as "$".
        lia.
      }
      iFrame.
      iModIntro.
      iLeft.
      iNext.
      iDestruct "HN" as "[_ $]".
    }
    {
      iDestruct "HN" as "[#Hlseq_lb_req HN]".
      iDestruct "HN" as "[>Hbad|Hreply_post]".
      { by iDestruct (own_valid_2 with "Hγpost Hbad") as %Hbad. }
      iMod ("HNClose" with "[Hγpost]") as "_".
      {
        iNext.
        iFrame "Hcseq_lb_strict".
        iRight.
        iFrame "# ∗".
      }
      iDestruct "Hreply_post" as (last_reply) "[#Hreply Hpost]".
      iModIntro.
      iFrame.
      iRight.
      iExists _; iFrame.
    }
Qed.

Lemma quiesce_idemp γrpc cid seqno Q PreCond PostCond :
  cid fm[[γrpc.(cseq)]]≥ int.nat seqno -∗
  □(▷Q -∗ (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))) -∗
  quiesceable_pre γrpc cid Q (PostCond) -∗
  quiesceable_pre γrpc cid PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb #Hwand Hatomic_pre".
  iModIntro.
  iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_agree_lb with "Hcown Hseqno_lb") as %Hseqno_ineq.

  iDestruct ("Hatomic_pre" $! seq with "Hcown") as ">[Hcown Hfupd]".
  iFrame.
  unfold laterable.make_laterable.
  iDestruct "Hfupd" as (S) "[HS #Hfupd]".
  iExists S.
  iModIntro.
  iFrame "HS".
  iModIntro.
  iIntros "HS".
  iSpecialize ("Hfupd" with "HS").
  iApply (rpc_atomic_pre_fupd_mono_strong with "[Hwand] Hfupd").
  iIntros "HQR #Hlb Hγproc".
  iDestruct (fmcounter_map_mono_lb (int.nat seqno) with "Hlb") as "#Hlb_seqno".
  { lia. }
  iDestruct "HQR" as "[HQ | HRpost]".
  {
    iDestruct ("Hwand" with "HQ") as "Hfupd".
    iDestruct ("Hfupd" with "Hγproc Hlb_seqno") as "HH".
    (* TODO: Show that mask of seqno is in mask of seq *)
    (* by iModIntro. *)
    admit.
  }
  { iFrame. by iModIntro. }
Admitted.

Lemma quiesce_intro γrpc cid seqno PreCond PostCond :
  PreCond -∗ (quiesce_fupd γrpc cid seqno PreCond PostCond).
Proof.
  iIntros.
  iExists (PreCond)%I.
  iFrame.
  iModIntro; iFrame.
  iIntros.
  iIntros "Hγproc #Hlb".
  iFrame.
    by iModIntro.
Qed.

Definition quiesce_fupd_raw γrpc cid seqno PreCond PostCond : iProp Σ :=
  (rpc_atomic_pre_fupd γrpc cid seqno (▷ PreCond ∨ ▷ ∃ ret:u64, PostCond ret))%I.

Lemma quiesceable_pre_instantiate γrpc cid seqno PreCond PostCond :
  RPCClient_own γrpc cid seqno -∗
  quiesceable_pre γrpc cid PreCond PostCond ={⊤}=∗
  RPCClient_own γrpc cid seqno ∗
  (quiesce_fupd γrpc cid seqno PreCond PostCond).
Proof.
  iIntros "Hcrpc Hqpre".
  iDestruct (own_discrete_elim with "Hqpre") as "Hqpre".
  iMod ("Hqpre" $! seqno with "Hcrpc") as "[Hcrpc Hfupd]".
  iModIntro. iFrame.
Qed.

Lemma wpc_RPCClient__MakeRequest k (f:goose_lang.val) cl_ptr cid γrpc args (PreCond:iProp Σ) PostCond {_:Discretizable (PreCond)} {_:∀ reply, Discretizable (PostCond reply)}:
  □(∀ seqno Q, (□(Q -∗ quiesce_fupd_raw γrpc cid seqno PreCond PostCond) -∗ is_rpcHandler f γrpc args {| Req_CID:=cid; Req_Seq:=seqno |}  Q PostCond)) -∗
  {{{
    quiesceable_pre γrpc cid PreCond PostCond ∗
    own_rpcclient cl_ptr γrpc cid ∗
    is_RPCServer γrpc
  }}}
    RPCClient__MakeRequest #cl_ptr f (into_val.to_val args) @ k ; ⊤
  {{{ (retv:u64), RET #retv; own_rpcclient cl_ptr γrpc cid ∗ ▷ PostCond retv }}}
  {{{ quiesceable_pre γrpc cid PreCond PostCond }}}.
Proof using Type*.
  iIntros "#Hfspec" (Φ Φc) "!# [Hpre [Hclerk #Hlinv]] HΦ".
  iNamed "Hclerk".

  Opaque quiesceable_pre.
  iCache with "Hpre HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iFrame.
  }
  wpc_rec _.
  { iFromCache. }

  iCache with "Hpre HΦ".
  { (* repeat crash proof *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iFrame.
  }
  wpc_pures.
  wpc_loadField.
  wpc_wpapply (overflow_guard_incr_spec).
  iIntros (HincrSafe).
  iNamed 1.

  wpc_pures.
  wpc_loadField.
  wpc_loadField.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (req_ptr) "Hreq".
  iNamed 1.
  iDestruct (struct_fields_split with "Hreq") as "(HCID&HSeq&HArgs&_)".
  iMod (readonly_alloc_1 with "HCID") as "#HCID".
  iMod (readonly_alloc_1 with "HSeq") as "#HSeq".
  iMod (readonly_alloc_1 with "HArgs") as "#HArgs".

  wpc_pures.
  wpc_loadField.
  wpc_pures.
  wpc_storeField.
  wpc_pures.
  wpc_wpapply wp_ref_to; first eauto.
  iIntros (errb_ptr) "Herrb_ptr".
  iNamed 1.

  wpc_pures.
  wpc_wpapply (wp_allocStruct); first eauto.
  iIntros (reply_ptr) "Hreply".
  iNamed 1.
  wpc_pures.
  iDestruct (fmcounter_map_get_lb with "Hcrpc") as "#Hcseqno_lb". (* Need this to apply quiesce_idemp_1 *)
  iMod (quiesceable_pre_instantiate with "Hcrpc Hpre") as "[Hcrpc Hqfupd]".
  unfold quiesce_fupd, laterable.make_laterable.
  iDestruct "Hqfupd" as (Q) "[HQ #Hqwand]".
  iMod (make_request {| Req_CID:=cid; Req_Seq:=cseqno|} Q PostCond with "[Hlinv] [Hcrpc] [HQ]") as "[Hcseq_own HallocPost]"; eauto.
  { simpl. word. }
  iDestruct "HallocPost" as (γP) "[#Hreqinv_init HγP]".
  (* Prepare the loop invariant *)
  iAssert (∃ (err:bool), errb_ptr ↦[boolT] #err)%I with "[Herrb_ptr]" as "Herrb_ptr".
  { iExists _. done. }
  iAssert (∃ reply', own_reply reply_ptr reply')%I with "[Hreply]" as "Hreply".
  { iDestruct (struct_fields_split with "Hreply") as "(?& ? & _)".
    iExists {| Rep_Ret:=_; Rep_Stale:=false |}. iFrame. }

  wpc_bind (For _ _ _). iApply (wpc_forBreak_cond' with "[-]").
  { by iNamedAccu. }
  {
    iNamed 1.
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hquiesce_req".
    iDestruct (quiesce_idemp γrpc cid with "Hcseqno_lb Hqwand Hquiesce_req") as "$".
  }
  {
    iIntros "!# __CTX"; iNamed "__CTX".

    iCache with "HγP HΦ".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro. iApply "HΦc".
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hquiesce_req".
      iDestruct (quiesce_idemp γrpc cid with "Hcseqno_lb Hqwand Hquiesce_req") as "$".
    }

    iDestruct "Hreply" as (reply') "Hreply".
    wpc_pures.
    wpc_bind (RemoteProcedureCall _ _ _). wpc_frame.
    wp_apply (RemoteProcedureCall_spec with "[] [$Hreply]").
    { iSpecialize ("Hfspec" $! cseqno Q with "[Hqwand]").
      { iModIntro. iIntros "HQ".
        iSpecialize ("Hqwand" with "HQ").
        iFrame.
      }
      iFrame "Hfspec". }
    {
      iSplit; last first.
      { unfold read_request.
        iFrame "#∗".
        simpl. iPureIntro. lia.
      }
      iFrame "Hreqinv_init".
    }
    iIntros (v) "Hrpc_post". iNamed 1.
    iDestruct "Herrb_ptr" as (err') "Herrb_ptr".

    iDestruct "Hrpc_post" as (reply) "[Hreply [#Hre | [#Hre HCallPost]]]".
    {
      iDestruct "Hre" as %->.

      wpc_bind (store_ty _ _).
      wpc_frame.
      wp_store.
      iNamed 1.
      wpc_pures.
      wpc_bind (load_ty _ _).
      wpc_frame.
      wp_load.
      iNamed 1.
      wpc_pures.
      iLeft.
      iFrame.
      iSplitL ""; first done.
      iSplitL "Herrb_ptr"; eauto.
    }

    iDestruct "Hre" as %->.

    wpc_bind (store_ty _ _).
    wpc_frame.
    wp_store.
    iNamed 1.

    wpc_pures.

    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    iApply wpc_fupd.
    wpc_pures.
    iRight.
    iSplitL ""; first by iModIntro.

    iDestruct "HCallPost" as "[ [_ Hbad] | #Hrcptstoro]"; simpl.
    {
      iDestruct (client_stale_seqno with "Hbad Hcseq_own") as %bad. exfalso.
      simpl in bad. replace (int.nat (word.add cseqno 1))%nat with (int.nat cseqno + 1)%nat in bad by word.
      lia.
    }

    iModIntro.
    iSplit; last first.
    {
      iLeft in "HΦ". iModIntro.
      iApply "HΦ".
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hquiesce_req".
      iDestruct (quiesce_idemp γrpc cid with "Hcseqno_lb Hqwand Hquiesce_req") as "$".
    }

    wpc_pures.
    iNamed "Hreply".
    replace (RPCReply.S) with (lockservice_nocrash.RPCReply.S) by done.
    replace (lockservice_nocrash.RPCReply.S) with (RPCReply.S) by done.

    iApply wpc_fupd.
    wpc_frame.
    wp_loadField.
    iNamed 1.

    iMod (get_request_post with "Hreqinv_init Hrcptstoro HγP") as "HP"; first done.
    simpl.
    iModIntro.
    iRight in "HΦ".
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
    iPureIntro.
    word.
  }
Qed.
End rpc_proof.

Section kv_proof.
Context `{!heapG Σ}.
Context `{!kvserviceG Σ}.
Variable γ:kvservice_names.

Definition own_kvclerk γ ck_ptr srv cid : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN) cid.

Lemma KVServer__Get_is_rpcHandler {E} srv old_v cid :
is_kvserver γ srv -∗
{{{
    True
}}}
    KVServer__Get #srv @ E
{{{ (f:goose_lang.val), RET f;
    ∀ args, (□ ∀ seqno Q, □(Q -∗ (quiesce_fupd_raw γ.(ks_rpcGN) cid seqno (Get_Pre γ old_v args) (Get_Post γ old_v args)))-∗
        is_rpcHandler f γ.(ks_rpcGN) args {|Req_CID:=cid; Req_Seq:=seqno|} Q (Get_Post γ old_v args))
}}}.
Proof.
  iIntros "#His_kv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (args req) "!#". iIntros (Q) "#HwandQ".
  iApply is_rpcHandler_eta.
  iIntros "!#" (replyv reqv).
  simpl.
  iAssert (is_kvserver γ srv) with "His_kv" as "His_kv2".
  iNamed "His_kv2".
  wp_loadField.
  wp_apply (RPCServer__HandleRequest_is_rpcHandler with "[] [] [His_kv]").
  {
    (* TODO: write core spec using HwandQ *)
    admit.
  }
  {
    (* TODO: use wpc_WriteDurableKVServer *)
    admit.
  }
  {
    (* TODO: use durable is_kvserver *)
    admit.
  }
  iIntros (f) "His_rpcHandler".
  iFrame.
Admitted.

Definition arg_of_key key := {|U64_1:= key; U64_2:=0 |}.

Lemma wpc_KVClerk__Get k (kck srv:loc) (cid old_v:u64) (key:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk γ kck srv cid ∗
       quiesceable_pre γ.(ks_rpcGN) cid (Get_Pre γ old_v (arg_of_key key)) (Get_Post γ old_v (arg_of_key key))
  }}}
    KVClerk__Get #kck #key @ k; ⊤
  {{{
      RET #old_v;
      own_kvclerk γ kck srv cid ∗
      (key [[γ.(ks_kvMapGN)]]↦ old_v )
  }}}
  {{{
       quiesceable_pre γ.(ks_rpcGN) cid (Get_Pre γ old_v (arg_of_key key)) (Get_Post γ old_v (arg_of_key key))
  }}}
.
Proof.
  iIntros "#His_kv !#" (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hq)".
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque quiesceable_pre.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_call.
  { done. }
  iCache with "Hq HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque quiesceable_pre.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_pures.
  iNamed "Hclerk".
  wpc_loadField.

  wpc_bind (KVServer__Get _).
  wpc_frame.
  wp_apply (KVServer__Get_is_rpcHandler _ old_v cid with "His_kv").
  iIntros (f) "#Hfspec".
  iNamed 1.

  wpc_loadField.
  pose (args:=arg_of_key key).
  replace (#key, (#0, #()))%V with (into_val.to_val args) by done.
  iDestruct ("Hfspec" $! args) as "#Hfspec2".
  iApply wpc_fupd.
  wpc_apply (wpc_RPCClient__MakeRequest with "Hfspec2 [Hq Hcl His_kv]").
  { iNamed "His_kv". iFrame. iNamed "His_rpc".
    iFrame "#".
  }
  iSplit.
  {
    by iLeft in "HΦ".
  }
  iNext.
  iIntros (retv) "[Hcl >Hpost]".
  iRight in "HΦ". iModIntro.
  unfold Get_Post.
  iDestruct "Hpost" as (->) "Hptsto".
  iApply "HΦ".
  iFrame "Hptsto".
  iExists _; iFrame.
Qed.

Lemma wpc_KVClerk__Put k E (kck srv:loc) (cid key value:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk γ kck srv cid ∗
       quiesceable_pre γ.(ks_rpcGN) cid (Put_Pre γ (mkRPCValsC key value)) (Put_Post γ (mkRPCValsC key value))
  }}}
    KVClerk__Put #kck #key #value @ k; E
  {{{
      RET #();
      own_kvclerk γ kck srv cid ∗
      ((key [[γ.(ks_kvMapGN)]]↦ value ) ∧
       quiesceable_pre γ.(ks_rpcGN) cid (Put_Pre γ (mkRPCValsC key value)) (Put_Post γ (mkRPCValsC key value)))
  }}}
  {{{
       quiesceable_pre γ.(ks_rpcGN) cid (Put_Pre γ (mkRPCValsC key value)) (Put_Post γ (mkRPCValsC key value))
  }}}.
Admitted.

End kv_proof.

Section incr_proof.

(* Proof for increment backed by kv service
   requires taking
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Variable γback:kvservice_names.

Context `{!kvserviceG Σ}.

Record incrservice_names := IncrServiceGN {
  incr_rpcGN : rpc_names;
  (* fmcounter_map of key -> counter value *)
  incr_mapGN : gname;
}.

Variable γ:incrservice_names.
Variable old_v:u64.
Variable incr_cid:u64.
(* This is constant for a particular IncrServer *)

Record IncrServerC := mkIncrServserC
{
  incr_seq: u64 ;
  incr_kvserver: loc ; (* This would be an IP address or some such *)
}.

Implicit Types server : IncrServerC.

Definition IncrServer_core_own_vol (srv:loc) server : iProp Σ :=
  ∃ (kck:loc),
  "Hkvserver" ∷ srv ↦[IncrServer.S :: "kvserver"] #(server.(incr_kvserver)) ∗
  "Hkck" ∷ srv ↦[IncrServer.S :: "kck"] #kck ∗
  "#His_kvserver" ∷ is_kvserver γback server.(incr_kvserver) ∗
  "Hkck_own" ∷ own_kvclerk γback kck server.(incr_kvserver) incr_cid
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
  .

Definition IncrServer_core_own_ghost server : iProp Σ :=
  "#His_kvserver" ∷ is_kvserver γback server.(incr_kvserver) ∗
  "Hrpcclient_own" ∷ RPCClient_own γback.(ks_rpcGN) (incr_cid) server.(incr_seq)
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
.

Definition IncrCrashInvariant (sseq:u64) (args:RPCValsC) : iProp Σ :=
  (* Case 1: Before crash barrier *)
  ("Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ [] ∗
   "Hq" ∷ quiesceable_pre γback.(ks_rpcGN) incr_cid (Get_Pre γback old_v args) (Get_Post γback old_v args)
   ) ∨

  (* Case 2: After crash barrier *)
  ( ∃ data,
  "Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ data ∗
  "%Hencoding" ∷ ⌜has_encoding data [EncUInt64 old_v]⌝ ∗
   "Hq" ∷ quiesceable_pre γback.(ks_rpcGN) incr_cid (Put_Pre γback ({|U64_1:=args.(U64_1) ; U64_2:=(word.add old_v 1)|}) ) (Put_Post γback ({|U64_1:=args.(U64_1) ; U64_2:=(word.add old_v 1)|}) )
  )
.

Instance CrashInv_disc sseq args : (Discretizable (IncrCrashInvariant sseq args)).
Proof.
Admitted.

Lemma increment_core_idempotent (isrv:loc) server (seq:u64) (args:RPCValsC) :
  {{{
       IncrCrashInvariant seq args ∗
       IncrServer_core_own_vol isrv server ∗
       IncrServer_core_own_ghost server
  }}}
    IncrServer__increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #0; True
  }}}
  {{{
       IncrCrashInvariant seq args ∗
       IncrServer_core_own_ghost server
  }}}.
Proof.
  iIntros (Φ Φc) "(HincrCrashInv & Hvol & Hghost) HΦ".
  wpc_call.
  { iFrame. }
  { iFrame. }
  unfold IncrCrashInvariant.
  iCache with "HincrCrashInv Hghost HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]". iModIntro. iApply "HΦc".
    iFrame.
  }
  wpc_pures.

  wpc_bind (ref #0)%E.
  wpc_frame.
  wp_apply (typed_mem.wp_AllocAt).
  {
    instantiate (1:=uint64T).
    eauto.
  }
  iIntros (l) "Hl". iNamed 1.
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.
  wpc_pures.

  iDestruct "HincrCrashInv" as "[Hcase|Hcase]"; iNamed "Hcase".
  { (* Case Get not done *)
    iCache with "Hfown_oldv Hq HΦ Hghost".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "Hq") as "Hq".
      iModIntro. iApply "HΦc".
      iFrame. iLeft. iFrame.
    }
    (* How to get rid of bdisc: iDestruct (own_discrete_elim with "Hq") as "Hq". *)
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "Hq") as "Hq".
      iModIntro. iIntros.
      iApply "HΦc".
      iFrame. iLeft. iFrame.
    }
    iNext.
    iIntros (content) "[Hcontent_slice Hfown_oldv]".
    wpc_pures.

    wpc_bind (slice.len _).
    wpc_frame.
    wp_apply wp_slice_len.
    iNamed 1.

    wpc_pures.
    iDestruct (slice.is_slice_sz with "Hcontent_slice") as "%Hslice_len".
    simpl in Hslice_len.
    assert (int.Z content.(Slice.sz) = 0) as -> by word.
    destruct bool_decide eqn:Hs.
    {
      apply bool_decide_eq_true in Hs.
      iExFalso; iPureIntro.
      done.
    }

    (* case that no durable oldv chosen *)
    wpc_pures.
    iNamed "Hvol".

    wpc_bind (struct.loadF _ _ _).
    wpc_frame.
    wp_loadField.
    iNamed 1.


    wpc_apply (wpc_KVClerk__Get with "His_kvserver [$Hkck_own $Hq]").
    iSplit.
    {
      iLeft in "HΦ".
      iModIntro. iIntros.
      iApply "HΦ".
      iFrame.
      iLeft.
      iFrame.
    }
    iNext.
    iIntros "[Hkck_own Hkvptsto]".

    iCache with "Hkvptsto HΦ Hghost Hfown_oldv".
    {
      iLeft in "HΦ".
      iModIntro.
      iApply "HΦ".
      iFrame "Hghost".
      iLeft.
      iFrame.
      (* TODO: Make a lemma that PreCond -∗ quiesceable_pre ... (PreCond) ...*)
      admit.
    }
    wpc_bind (store_ty _ _).
    wpc_frame.
    wp_store.
    iNamed 1.

    wpc_pures.
    wpc_bind (marshal.NewEnc _).
    wpc_frame.
    wp_apply (wp_new_enc).
    iIntros (enc_v) "Henc".
    iNamed 1.

    wpc_pures.
    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.

    wpc_bind (marshal.Enc__PutInt _ _).
    wpc_frame.
    wp_apply (wp_Enc__PutInt with "Henc"); first word.
    iIntros "Henc". iNamed 1.

    wpc_pures.
    wpc_bind (marshal.Enc__Finish _).
    wpc_frame.
    wp_apply (wp_Enc__Finish with "Henc").
    iIntros (content_slice data) "(%Hencoding & %Hlength & Hslice)".
    iNamed 1.

    wpc_apply (wpc_Write with "[$Hfown_oldv $Hslice]").
    iSplit.
    { (* Prove that if Write crashes, our crash condition is still met *)
      iLeft in "HΦ".
      iModIntro.
      iIntros "[Hfown|Hfown]".
      { (* write didn't go through *)
        iApply "HΦ".
        iFrame.
        iLeft; iFrame.
        admit. (* TODO: MakeRequest should return `PostCond ∧ quiesceable_pre`! *)
      }
      { (* Wrote oldv *)
        iApply "HΦ".
        iFrame.
        iRight.
        iExists _; iFrame.
        simpl in Hencoding.
        iSplitL ""; first done.
        (* TODO: Put_Pre -> quiesceable_pre (Put_Pre) *)
        admit.
      }
    }
    iNext.
    iIntros "[Hfown Hslice]".

    iCache with "Hfown HΦ Hghost Hkvptsto".
    {
      (* Repeat above *)
      admit.
    }

    wpc_pures.
    wpc_bind (load_ty _ _).
    wpc_frame.
    wp_load.
    iNamed 1.
    wpc_pures.

    wpc_loadField.

    wpc_apply (wpc_KVClerk__Put with "His_kvserver [$Hkck_own Hkvptsto]").
    { admit. (* TODO: quiesceable_intro *) }
    iSplit.
    {
      iLeft in "HΦ".
      iModIntro.
      iIntros.
      iApply "HΦ".
      iFrame.
      iRight.
      iExists _; iFrame.
      replace ((Z.of_nat 1)) with (1)%Z by eauto.
      done.
    }
    iNext.

    iIntros "[Hkck_own HputPost]".

    wpc_pures.
    {
      iRight in "HputPost".
      iLeft in "HΦ".
      Opaque quiesceable_pre.
      iModIntro.
      iApply "HΦ".
      iFrame "Hghost".
      iRight.
      iExists _; iFrame.
      done.
    }

    iRight in "HΦ".
    iApply "HΦ".
    done.
  }
  { (* Case get already done *)
    (* TODO: Merge if/then/rest from above *)
    admit.
  }
Admitted.

End incr_proof.
