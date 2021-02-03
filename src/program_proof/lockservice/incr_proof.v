From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section incr_proof.

(* Proof for increment backed by kv service
   requires taking
 *)

Context `{!heapG Σ}.
Context `{!filesysG Σ}.

Variable γback:kvservice_names.

Context `{!kvserviceG Σ}.

(* This is the double-fupd crash obligation. *)
Definition KVGetPreClientWeak (cid:u64) (γrpc:rpc_names) (PreCond:iProp Σ): iProp Σ :=
  ∀ (seq:u64), cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗ (
            cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
                   (own γrpc.(proc) (Excl ()) ∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq) ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ PreCond
  ).
(*
  Should use up previous γPost to prove this fupd.
  We want to be able to show →
 *)

Definition IdempotentPre γrpc (cid seq:u64) (PreCond : RPCValC → iProp Σ) : (RPCValC → iProp Σ) :=
  λ (args:RPCValC),
        (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ PreCond args)%I.

Lemma server_takes_idempotent_request γrpc γreq (cid key va:u64) PreCond PostCond req lastSeqM lastReplyM:
  (int.Z (map_get lastSeqM req.(Req_CID)).1 < int.Z req.(Req_Seq))%Z →
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq (IdempotentPre γrpc req.(Req_CID) req.(Req_Seq) PreCond) (PostCond) req -∗
  RPCServer_own γrpc lastSeqM lastReplyM ={⊤}=∗
  PreCond req.(Req_Args) ∗
  RPCServer_own_processing γrpc req lastSeqM lastReplyM.
Proof.
  intros Hrseq.
  iIntros "HserverInv HreqInv Hsown".

  iInv "HreqInv" as "[#>Hreqeq_lb Hcases]" "HMClose".
  iNamed "Hsown".

  iDestruct "Hcases" as "[[>Hunproc [>Hbad|Hpre]]|[#>Hlseq_lb _]]".
  {
    iDestruct (own_valid_2 with "Hproc_own Hbad") as %H; contradiction.
  }
  {
    iDestruct "Hpre" as "[>HγPre HidemPre]".
    iSpecialize ("HidemPre" with "[Hproc_own]").
    {  done. }
    (* Expectedly stuck trying to show req.cid fm[lseq]≥ req.seq to use the
       HidemPre fupd Indeed, we won't be able to take PreCond out of the old
       request until we actually update the seqno on durable storage. Otherwise,
       we could be holding the proc token, so we know no one else is currently
       processing the old request, then we steal PreCond from the old request
       invariant, then we could crash before we update lastSeq, and then after
       restarting, the old request might *actually* be run again, so it needs
       its PreCond.

       So, we can only actually get the PreCond as soon as we actually update
       the lastSeq. This means the core function would not be given [PreCond], but
       [(own proc ∗ fm[lseq]≥ fact) ={⊤}=∗ PreCond].

       This'll also mean the fupd where we go from PreCond -> PostCond must
       happen at the same time as the lseq update.
     *)
Abort.

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
  "Hkck_own" ∷ own_kvclerk γback kck server.(incr_kvserver)
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
  .

Definition IncrServer_core_own_ghost server : iProp Σ :=
  "#His_kvserver" ∷ is_kvserver γback server.(incr_kvserver) ∗
  "Hrpcclient_own" ∷ RPCClient_own γback.(ks_rpcGN) (incr_cid) server.(incr_seq)
  (* This is using the non-crash-safe version of kvserver in kv_proof.v *)
.

Definition idemp_fupd args : iProp Σ :=
    <bdisc> (∀ seq, incr_cid fm[[γback.(ks_rpcGN).(cseq)]]↦ seq ={⊤}=∗
      incr_cid fm[[γback.(ks_rpcGN).(cseq)]]↦ seq ∗
    IdempotentPre γback.(ks_rpcGN) incr_cid seq (Get_Pre γback old_v) args)
.

Global Instance idemp_fupd_disc args : (Discretizable (idemp_fupd args)).
Proof.
  rewrite /Discretizable.
  by rewrite -own_discrete_idemp.
Defined.

Definition IncrCrashInvariant (sseq:u64) (args:RPCValC) : iProp Σ :=
  (* Case 1: Before crash barrier *)
  ("Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ [] ∗
   "HidemPre" ∷ idemp_fupd args
   ) ∨

  (* Case 2: After crash barrier *)
  ( ∃ data,
  "Hfown_oldv" ∷ (("incr_request_" +:+ u64_to_string sseq) +:+ "_oldv") f↦ data ∗
  "%Hencoding" ∷ ⌜has_encoding data [EncUInt64 old_v]⌝
  )
.


Instance CrashInv_disc sseq  args : (Discretizable (IncrCrashInvariant sseq args)) := _.
(*
Proof.
  rewrite /Discretizable.
  iIntros "[H|H]".
  - iNamed "H".
    rewrite own_discrete_idemp.
    iModIntro.
    iLeft. iFrame.
  - iModIntro. iRight. iFrame.
Defined.
 *)

Lemma increment_core_indepotent (isrv:loc) server (seq:u64) (args:RPCValC) :
  {{{
       IncrCrashInvariant seq args ∗
       IncrServer_core_own_vol isrv server ∗
       IncrServer_core_own_ghost server
  }}}
    IncrServer__increment_core #isrv #seq (into_val.to_val args) @ 37 ; ⊤
  {{{
      RET #(); True
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
  wp_apply (wp_alloc_untyped); first done.
  iIntros (l) "Hl". iNamed 1.
  wpc_pures.

  wpc_bind (grove_ffi.U64ToString _).
  wpc_frame.
  wp_apply wp_U64ToString.
  iNamed 1.
  wpc_pures.

  iDestruct "HincrCrashInv" as "[Hcase|Hcase]"; iNamed "Hcase".
  {
    iCache with "Hfown_oldv HidemPre HΦ Hghost".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "HidemPre") as "HidemPre".
      iModIntro. iApply "HΦc".
      iFrame. iLeft. iFrame.
    }
    (* How to get rid of bdisc: iDestruct (own_discrete_elim with "HidemPre") as "HidemPre". *)
    wpc_apply (wpc_Read with "Hfown_oldv").
    iSplit.
    { (* Show that the crash obligation of the function we're calling implies our crash obligation *)
      iDestruct "HΦ" as "[HΦc _]".
      iDestruct (own_discrete_idemp with "HidemPre") as "HidemPre".
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

    (* TODO: Move this to a new spec/proof for KVClerk__Get *)
    iDestruct (own_discrete_elim with "HidemPre") as "HidemPre".
    iNamed "Hkck_own".
    iNamed "Hcl".

    (* TODO: own_kvclerk needs to expose cid for this to work *)
    replace (cid) with (incr_cid) in * by admit.
    iMod ("HidemPre" with "Hcrpc") as "(Hcrpc & HidemPre)".

    (* Use IdempotentPre (GetPre) to call KVClerk__Get
       The crash condition of KVClerk__Get needs to be the
       IdempotentPre-granting-fupd
     *)

Admitted.

End incr_proof.

Section rpc_proof.
Context `{!heapG Σ}.
Context `{!rpcG Σ u64}.

(* This is the fupd that the server uses to get the (PreCond ∨ PostCond) of an old request after increasing seqno to quiesce it *)
Definition quiesce_fupd γrpc (cid seq:u64) (PreCond : RPCValC → iProp Σ) (PostCond:RPCValC → u64 → iProp Σ) : (RPCValC → iProp Σ) :=
  λ (args:RPCValC),
        (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ ▷ (PreCond args ∨ (∃ reply,PostCond args reply)))%I.

(* TODO: Want a quiesce_fupd that gives a user-chosen resource so long as one provides a proof that (PreCond ∨ PostCond ={⊤}=∗ user-chosen-resource) *)
(* E.g. if we want to do a new Put() after giving up on a Get(), we should be able to quiesce the Get() and  *)

(* This gives the quiesce_fupd for any sequence number that the client can take on
   This is the precondition for ck.MakeRequest(args), where ck has the given cid *)
Definition quiesceable_pre γrpc cid args PreCond PostCond : iProp Σ :=
    <bdisc> (∀ seq, cid fm[[γrpc.(cseq)]]↦ int.nat seq ={⊤}=∗
      cid fm[[γrpc.(cseq)]]↦ int.nat seq ∗
   quiesce_fupd γrpc cid seq PreCond PostCond args)
.

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

Lemma quiesce_request (req:RPCRequest) γrpc γreq PreCond PostCond :
  is_RPCServer γrpc -∗
  is_RPCRequest γrpc γreq PreCond PostCond req -∗
  (RPCRequest_token γreq) -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
    iIntros "#Hsrpc #His_req Hγpost".
    (* iDestruct (fmcounter_map_get_lb with "Hcown") as "#Hcseq_lb". *)
    iModIntro.

    iIntros (new_seq) "Hcown".

    iInv "His_req" as "[>#Hcseq_lb_strict HN]" "HNClose".
    iMod ("HNClose" with "[$Hcseq_lb_strict $HN]") as "_".

    iDestruct (fmcounter_map_agree_lb with "Hcown Hcseq_lb_strict") as %Hnew_seq.
    iModIntro.
    iFrame.

    iIntros "Hγproc #Hlseq_lb".
    iInv "His_req" as "HN" "HNClose".
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
      iNext.
      iLeft.
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

(* Need to have the fmcounter fact because the quiesce_fupd in the
   quiesceable_pre is specialized to a particular seqno, while we need to know
   that any seqno is good. The fmcounter fact is one way to get around this.
   Alternatively, could also maybe make the RPCRequestInvariant contain
   (quiesce_fupd ∧ quiesceable_pre).
 *)
Lemma quiesce_idemp_1 γrpc req seqno PreCond PostCond:
  req.(Req_CID) fm[[γrpc.(cseq)]]≥ int.nat seqno -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond) PostCond -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
  iIntros "#Hseqno_lb Hqfupd".
  iModIntro. iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_agree_lb with "Hcown Hseqno_lb") as %Hseqno_ineq.

  iDestruct ("Hqfupd" $! seq with "Hcown") as ">[$ Hqfupd]".
  iModIntro.

  iIntros "Hγproc #Hlb".
  iDestruct ("Hqfupd" with "Hγproc Hlb") as ">[Hγproc [Hqfupd|Hreply]]".
  {
    iAssert (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond req.(Req_Args))%I with "[Hqfupd]" as "Hqfupd".
    { admit. } (* Need PreCond to be timeless for this to work out; too many laters *)
    iSpecialize ("Hqfupd" with "Hγproc").
    iDestruct (fmcounter_map_mono_lb (int.nat seqno) with "Hlb") as "#Hlseq_seqno_lb".
    { lia. }
    iSpecialize ("Hqfupd" with "Hlseq_seqno_lb").
    iFrame.
  }
  {
    iModIntro. iFrame.
  }
Admitted. (* timeless precond *)

Lemma quiesce_idemp_2 γrpc req seqno PreCond PostCond:
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args)
        (λ args, (quiesce_fupd γrpc req.(Req_CID) seqno PreCond PostCond args) ∧
           (quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond)
           )
        PostCond -∗
  quiesceable_pre γrpc req.(Req_CID) req.(Req_Args) PreCond PostCond.
Proof.
  iIntros "Hqfupd".
  iModIntro. iIntros (seq) "Hcown".
  iDestruct (fmcounter_map_get_lb with "Hcown") as "#Hlb".

  iDestruct ("Hqfupd" $! seq with "Hcown") as ">[$ Hqfupd]".
  iModIntro.
  iIntros "Hγproc #Hlb2".
  (* TODO: this would work out if quiesceable_pre required only an fm[[...]]≥ fact as input; luckily, we can do that! *)
  (*
  iSpecialize ("Hqfupd" with "Hγproc Hlb2").

  iDestruct ("Hqfupd" with "Hγproc Hlb") as ">[Hγproc [Hqfupd|Hreply]]".
  {
    iRight in "Hqfupd".
  } *)
Admitted.

Lemma wpc_RPCClient__MakeRequest k (f:goose_lang.val) cl_ptr cid args γrpc (PreCond:RPCValC -> iProp Σ) PostCond {_:Discretizable (PreCond args)} {_:∀ reply, Discretizable (PostCond args reply)}:
  (∀ seqno, is_rpcHandler f γrpc (quiesce_fupd γrpc cid seqno PreCond PostCond) PostCond) -∗
  {{{
    PreCond args ∗
    own_rpcclient cl_ptr γrpc cid ∗
    is_RPCServer γrpc
  }}}
    RPCClient__MakeRequest #cl_ptr f (into_val.to_val args) @ k ; ⊤
  {{{ (retv:u64), RET #retv; own_rpcclient cl_ptr γrpc cid ∗ PostCond args retv }}}
  {{{ quiesceable_pre γrpc cid args PreCond PostCond }}}.
Proof using Type*.
  iIntros "#Hfspec" (Φ Φc) "!# [Hprecond [Hclerk #Hlinv]] HΦ".
  iNamed "Hclerk".

  iCache with "Hprecond HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro.
    iApply "HΦc".
    iModIntro.
    iIntros.
    iModIntro.
    iFrame.
    iIntros.
    iModIntro; iFrame.
  }
  wpc_rec _.
  { iFromCache. }

  iCache with "Hprecond HΦ".
  { (* Use PreCond to show idemp_fupd *)
    iDestruct "HΦ" as "[HΦc _]".
    iModIntro. iApply "HΦc".
    iModIntro. iIntros.
    iModIntro. iFrame.
    iIntros. iModIntro; iFrame.
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

  iMod (make_request {| Req_Args:=args; Req_CID:=cid; Req_Seq:=cseqno|} (quiesce_fupd γrpc cid cseqno PreCond PostCond) PostCond with "[Hlinv] [Hcrpc] [Hprecond]") as "[Hcseq_own HallocPost]"; eauto.
  (* { admit. (* TODO: add assumption *) } *)
  { simpl. word. }
  { iIntros "??". iFrame. by iModIntro. }
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
    simpl.
    iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hquiesce_req".
    iDestruct (quiesce_idemp_1 with "[] Hquiesce_req") as "HH".
    { simpl. iFrame "#". }
    iFrame.
  }
  {
    iIntros "!# __CTX"; iNamed "__CTX".

    iCache with "HγP HΦ".
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro. iApply "HΦc".
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hq".
      iDestruct (quiesce_idemp_1 with "[] Hq") as "Hq".
      { simpl. iFrame "#". }
      iFrame.
    }

    iDestruct "Hreply" as (reply') "Hreply".
    wpc_pures.
    wpc_bind (RemoteProcedureCall _ _ _). wpc_frame.
    wp_apply (RemoteProcedureCall_spec with "[] [Hreply]").
    { iSpecialize ("Hfspec" $! cseqno). iFrame "Hfspec". }
    {
      iSplit; last first.
      { unfold read_request.
        instantiate (2:={|Req_CID:=_; Req_Seq := _; Req_Args := _ |}).
        iFrame "#".
        iFrame "Hreply".
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
      iDestruct (quiesce_request with "Hlinv Hreqinv_init HγP") as "Hq".
      iDestruct (quiesce_idemp_1 with "[] Hq") as "Hq".
      { simpl. iFrame "#". }
      iFrame.
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
    assert (Timeless (PostCond args reply.(Rep_Ret))) by admit. (* Timeless post *)
    iMod "HP".
    iModIntro.
    iRight in "HΦ".
    iApply "HΦ".
    iFrame.
    iExists _; iFrame.
    iPureIntro.
    word.
Admitted.
End rpc_proof.

Section kv_proof.
Context `{!heapG Σ}.
Context `{!kvserviceG Σ}.
Variable γ:kvservice_names.
Variable old_v:u64.

Definition own_kvclerk γ ck_ptr srv cid : iProp Σ :=
  ∃ (cl_ptr:loc),
   "Hcl_ptr" ∷ ck_ptr ↦[KVClerk.S :: "client"] #cl_ptr ∗
   "Hprimary" ∷ ck_ptr ↦[KVClerk.S :: "primary"] #srv ∗
   "Hcl" ∷ own_rpcclient cl_ptr γ.(ks_rpcGN) cid.

Lemma KVClerk__Get_spec k E (kck srv:loc) (cid key:u64) :
  is_kvserver γ srv -∗
  {{{
       own_kvclerk γ kck srv cid ∗
       (idemp_fupd γ old_v cid (key, (U64 0, ())))
  }}}
    KVClerk__Get #kck #key @ k; E
  {{{
      RET #old_v;
      own_kvclerk γ kck srv cid ∗
      (key [[γ.(ks_kvMapGN)]]↦ old_v )
  }}}
  {{{
       (idemp_fupd γ old_v cid (key, (U64 0, ())))
  }}}
.
Proof.
  iIntros "His_kv !#" (Φ Φc) "Hpre HΦ".
  iDestruct "Hpre" as "(Hclerk & Hidemp_fupd)".
  iCache with "Hidemp_fupd HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque idemp_fupd.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_call.
  { done. }
  iCache with "Hidemp_fupd HΦ".
  {
    iDestruct "HΦ" as "[HΦc _]".
    Opaque idemp_fupd.
    iModIntro.
    iApply "HΦc".
    done.
  }
  wpc_pures.
Admitted.

End kv_proof.
