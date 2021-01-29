From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet kv_proof fmcounter_map.
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
  We want to be able to show
 *)

Definition IdempotentPre γrpc (cid seq:u64) (PreCond : RPCValC → iProp Σ) : (RPCValC → iProp Σ) :=
  λ (args:RPCValC),
        (own γrpc.(proc) (Excl ()) -∗ cid fm[[γrpc.(lseq)]]≥ int.nat seq ={⊤}=∗ own γrpc.(proc) (Excl ()) ∗ PreCond args)%I.

Search fupd.

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

Instance idemp_fupd_disc args : (Discretizable (idemp_fupd args)).
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
    Search "bdisc".
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

  (* Use has_encoding data [] ∨ ... in invariant *)

Admitted.

End incr_proof.
