From Perennial.algebra Require Import auth_map.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang.lib Require Import slice.typed_slice.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc_logatom rpc nondet kv_proof fmcounter_map wpc_proofmode common_proof rpc_durable_proof.
Require Import Decimal Ascii String DecimalString.
From Perennial.goose_lang Require Import ffi.grove_ffi.

Section incr_proof.

(* Proof for increment backed by kv service
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
