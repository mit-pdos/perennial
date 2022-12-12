From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.simplepb Require Import config_proof pb_definitions pb_ghost pb_init_proof.
From Perennial.program_proof.simplepb Require Import kv_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.goose_lang Require Import crash_borrow crash_modality.

Section closed_wpcs.

(* FIXME: kv64G *)
Context `{!heapGS Σ}.
Context `{!kv64G Σ}.

Definition replica_fname := "kv.data".

Lemma wpc_kv_replica_main1 γsys γsrv Φc:
  ((∃ data' : list u8, replica_fname f↦data' ∗ ▷ file_crash (own_Server_ghost γsys γsrv) data') -∗
    Φc) -∗
  is_pb_host 1%Z γsys γsrv -∗ sys_inv γsys -∗
  (∃ data : list u8, replica_fname f↦data ∗ file_crash (own_Server_ghost γsys γsrv) data) -∗
  WPC kv_replica_main1 #() @ ⊤
  {{ _, True }}
  {{ Φc }}
.
Proof.
  iIntros "HΦc #Hpbhost #Hsys Hpre".
  iDestruct "Hpre" as (?) "[Hfile Hcrash]".

  unfold kv_replica_main1.
  wpc_call.
  { iApply "HΦc". iExists _. iFrame. }

  iCache with "HΦc Hfile Hcrash".
  { iApply "HΦc". iExists _. iFrame. }
  wpc_bind (Primitive2 _ _ _).
  wpc_frame.
  iApply wp_crash_borrow_generate_pre.
  { done. }
  wp_apply (wp_ref_of_zero).
  { done. }
  iIntros (?) "Hl".
  iIntros "Hpreborrow".
  iNamed 1.
  wpc_pures.
  wpc_bind (store_ty _ _).
  wpc_frame.
  wp_store.
  iModIntro.
  iNamed 1.

  iApply wpc_cfupd.
  wpc_apply (wpc_crash_borrow_inits with "Hpreborrow [Hfile Hcrash] []").
  { iAccu. }
  {
    iModIntro.
    instantiate (1:=(|C={⊤}=> ∃ data', replica_fname f↦ data' ∗ ▷ file_crash (own_Server_ghost γsys γsrv) data')).
    iIntros "[H1 H2]".
    iModIntro.
    iExists _.
    iFrame.
  }
  iIntros "Hfile_ctx".
  wpc_apply (wpc_crash_mono _ _ _ _ _ (True%I) with "[HΦc]").
  { iIntros "_".
    iIntros "H".
    iMod "H".
    iModIntro.
    iApply "HΦc".
    done. }
  iApply wp_wpc.
  wp_pures.

  wp_apply (wp_Start with "[Hfile_ctx]").
  {
    iFrame "∗#".
  }
  wp_pures.
  done.
Qed.

End closed_wpcs.
