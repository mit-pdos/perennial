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
            □ (P' -∗ KVServer_core_own_ghost γ kvserver -∗
               own γ.(ks_rpcGN).(proc) (Excl ()) -∗
               req.(Req_CID) fm[[γ.(ks_rpcGN).(lseq)]]≥ int.nat req.(Req_Seq)
               ={⊤∖↑rpcRequestInvN req}=∗ Put_Post γ args r ∗ KVServer_core_own_ghost γ kvserver')
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
  iIntros "HQ Hghost Hγproc #Hlb".
  iDestruct ("Hwand" with "HQ") as "Hfupd".
  unfold rpc_atomic_pre_fupd.
  iSpecialize ("Hfupd" with "Hγproc Hlb").
  (* own γproc ={⊤, ⊤ ∖ ↑oldRequestInvN}=∗ blah ∗ (blah ={⊤ ∖ ↑oldRequestInvN, ⊤}=∗ RESOURCES ∗ own γproc)
     |={⊤, ⊤ ∖ ↑newRequestInvN}=> (own γproc ∗ (POST ∨ PRE ={⊤ ∖ ↑newRequestInvN, ⊤}=∗ own γproc)

     (PRE ∗ ctx ==∗ POST ∗ ctx')

   *)
  iDestruct (fupd_mask_weaken _ (rpcReqInvUpToN req.(Req_Seq)) with "Hfupd") as ">Hfupd".
  {
    apply subseteq_difference_r.
    - admit. (* Use defining property of rpcReqInvUpToN *)
    - set_solver.
  }
  iMod "Hfupd".
  (* TODO: strengthen fupd postcond to have γproc and cid ≥ fact *)
Admitted.

End kv_logatom_proof.
