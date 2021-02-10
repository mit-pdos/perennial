From iris.program_logic Require Export weakestpre.
From Perennial.goose_lang Require Import prelude.
From Perennial.goose_lang Require Import ffi.disk_prelude.
From Perennial.goose_lang Require Import notation.
From Perennial.program_proof Require Import proof_prelude.
From RecordUpdate Require Import RecordUpdate.
From Perennial.algebra Require Import auth_map.
From Perennial.goose_lang.lib Require Import lock.
From Perennial.goose_lang.lib Require Import crash_lock.
From Perennial.Helpers Require Import NamedProps.
From Perennial.Helpers Require Import ModArith.
From Goose.github_com.mit_pdos.lockservice Require Import lockservice.
From Perennial.program_proof Require Import proof_prelude marshal_proof.
From Perennial.goose_lang Require Import ffi.grove_ffi.
From Perennial.program_proof.lockservice Require Import rpc_proof rpc nondet fmcounter_map rpc_durable_proof kv_proof kv_durable incr_proof wpc_proofmode.

Section kv_logatom_proof.
Context `{!heapG Σ, !kvserviceG Σ, stagedG Σ}.
Context `{!filesysG Σ}.

Lemma wpc_put_logatom_core γ (srv:loc) args req kvserver Q:
□(Q -∗ (rpc_atomic_pre_fupd γ.(ks_rpcGN) req.(Req_CID) req.(Req_Seq) (Put_Pre γ args))) -∗
{{{
     (kv_core_mu srv γ).(core_own_vol) kvserver ∗
     <disc> Q
}}}
  KVServer__put_core #srv (into_val.to_val args) @ 36 ; ⊤
{{{
      kvserver' (r:u64) P', RET #r;
            (<disc> P') ∗
            KVServer_core_own_vol srv kvserver' ∗
            □ (P' -∗ Q) ∗
            □ (P' -∗
               own γ.(ks_rpcGN).(proc) (Excl ()) -∗
               req.(Req_CID) fm[[γ.(ks_rpcGN).(lseq)]]≥ int.nat req.(Req_Seq) -∗
               KVServer_core_own_ghost γ kvserver
               ={⊤∖↑rpcRequestInvN req}=∗ Put_Post γ args r ∗ own γ.(ks_rpcGN).(proc) (Excl ()) ∗
                                          KVServer_core_own_ghost γ kvserver')
}}}
{{{
     Q
}}}.
Proof.
  iIntros "#Hwand !#".
  iIntros (Φ Φc) "[Hvol Hpre] HΦ".
  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }
  wpc_call; first done.

  iCache with "Hpre HΦ".
  { iDestruct "HΦ" as "[HΦc _]". iModIntro. by iApply "HΦc". }

  wpc_pures.
  iNamed "Hvol".
  wpc_loadField.

  wpc_bind (MapInsert _ _ _).
  wpc_frame.

  wp_apply (wp_MapInsert with "HkvsMap"); eauto; iIntros "HkvsMap".
  iNamed 1.
  wpc_pures.
  iDestruct "HΦ" as "[_ HΦ]".
  iApply ("HΦ" $! {| kvsM := <[args.(U64_1):=args.(U64_2)]> kvserver.(kvsM) |} _ (Q)).
  iFrame.
  iSplitR "".
  { iExists _; iFrame. }

  iSplit; first eauto.

  (* The commit point fupd *)
  iModIntro.
  iIntros "HQ Hγproc #Hlb Hghost".
  iDestruct ("Hwand" with "HQ") as "Hfupd".
  unfold rpc_atomic_pre_fupd.
  iSpecialize ("Hfupd" with "Hγproc Hlb").
  (* own γproc ={⊤, ⊤ ∖ ↑oldRequestInvN}=∗ blah ∗ (blah ={⊤ ∖ ↑oldRequestInvN, ⊤}=∗ RESOURCES ∗ own γproc)
     |={⊤, ⊤ ∖ ↑newRequestInvN}=> (own γproc ∗ (POST ∨ PRE ={⊤ ∖ ↑newRequestInvN, ⊤}=∗ own γproc)

     (PRE ∗ ctx ==∗ POST ∗ ctx')

   *)

  iMod (fupd_intro_mask' _ _) as "Hclose"; last iMod "Hfupd" as "[$ Hpre]".
  {
    apply subseteq_difference_r; last set_solver.
    destruct req; simpl.
    symmetry.
    apply rpcReqInvUpToN_prop_2.
    lia.
  }
  iMod "Hclose" as "_".

  iDestruct "Hpre" as (v) "Hpre".
  iMod (map_update with "Hghost Hpre") as "[Hkvctx Hptsto]".

  iModIntro.
  iFrame.
Qed.

Lemma KVServer__Put_is_rpcHandler {E} γ srv rpc_srv cid :
is_kvserver γ srv rpc_srv -∗
{{{
    True
}}}
    KVServer__Put #srv @ E
{{{ (f:goose_lang.val), RET f;
    ∀ args, (□ ∀ seqno Q, □(Q -∗ (quiesce_fupd_raw γ.(ks_rpcGN) cid seqno (Put_Pre γ args) (Put_Post γ args)))-∗
        □(Q -∗ <disc> Q) -∗
        □(▷ Q -∗ ◇Q) -∗
        is_rpcHandler f γ.(ks_rpcGN) args {|Req_CID:=cid; Req_Seq:=seqno|} (Q) (Put_Post γ args))
}}}.
Proof.
  iIntros "#His_kv !#" (Φ) "_ HΦ".
  wp_lam.
  wp_pures.
  iApply "HΦ".
  iIntros (args req) "!#". iIntros (Q) "#HwandQ #HQdisc #HQtmless".
  iApply is_rpcHandler_eta.
  iIntros "!#" (replyv reqv).
  simpl.
  iAssert (_) with "His_kv" as "His_kv2".
  iNamed "His_kv2".
  wp_loadField.
  wp_apply (RPCServer__HandleRequest_is_rpcHandler KVServerC with "[] [] [His_kv]").
  {
    clear Φ.
    iIntros (server) "!#". iIntros (Φ Φc) "Hpre HΦ".
    iNamed "Hpre".
    iMod ("HQtmless" with "Hpre") as "HQ".
    iDestruct ("HQdisc" with "HQ") as "HQ".
    wpc_pures.
    {
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      by iApply "HΦc".
    }

    iApply (wpc_put_logatom_core γ _ _ {|Req_CID:=_; Req_Seq:= _ |} with "[] [HQ Hvol]").
    { (* Prove fupd; TODO: this should happen at a higher level, and this should just talk about rpc_atomic_pre_fupd *)
      iModIntro. simpl. unfold quiesce_fupd_raw.
      iIntros "HQ".
      iDestruct ("HwandQ" with "HQ") as "Hfupd".
      iApply (rpc_atomic_pre_fupd_mono_strong with "[] Hfupd").
      iIntros "[>$|>Hcase] _ $".
      { by iModIntro. }
      { iModIntro. iNamed "Hcase". iExists _. iFrame "Hcase". }
    }
    {
      iFrame "HQ".
      iFrame "Hvol".
    }
    iSplit.
    {
      iLeft in "HΦ".
      done.
    }
    iNext.
    iIntros (server' r P') "(HP' & Hvol & Hpre & Hfupd)".
    iRight in "HΦ".
    iApply "HΦ".
    iFrame "HP' Hpre Hvol".
    iFrame "Hfupd".
  }
  {
    iIntros (server rpc_server server' rpc_server') "!#".
    clear Φ.
    iIntros (Φ Φc) "Hpre HΦ".
    wpc_pures.
    {
      iDestruct "Hpre" as "(_ & _ & Hdur)". (* Requires own_durable to be discretizable *)
      iDestruct "HΦ" as "[HΦc _]".
      iModIntro.
      iApply "HΦc".
      by iLeft.
    }
    wpc_apply (wpc_WriteDurableKVServer with "Hsv Hpre").
    iSplit.
    {
      by iDestruct "HΦ" as "[HΦc _]".
    }
    iNext. by iDestruct "HΦ" as "[_ HΦ]".
  }
  {
    iFrame "His_server".
  }
  iIntros (f) "His_rpcHandler".
  iFrame.
Qed.

End kv_logatom_proof.
