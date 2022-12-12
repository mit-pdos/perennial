From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.simplepb Require Import config_proof pb_definitions pb_ghost pb_init_proof.
From Perennial.program_proof.simplepb Require Import kv_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof.simplepb.apps Require Import closed_wpcs.
From Perennial.goose_lang Require Import crash_borrow crash_modality.

Module closed.

Import adequacy dist_adequacy grove_ffi_adequacy dist_lang.

Definition grove_dist_adequate
           (enonidempσs: list (node_init_cfg (Λ:=goose_lang)))
           (ebσs: list (goose_lang.expr * goose_lang.state))
           (g: goose_lang.global_state) :=
  let ρs := fmap (λ ebσ, {| init_thread := fst ebσ;
                           init_restart := fst ebσ;
                           init_local_state := snd ebσ |})
               ebσs in
  dist_adequacy.dist_adequate (CS := goose_crash_lang) (enonidempσs ++ ρs) g.

Definition kv_pbΣ := #[heapΣ; simplelogΣ (sm_record:=kv_record); pbΣ (pb_record:=kv_record); ghost_varΣ (list u64); urpcregΣ].

Definition configHost : chan := U64 10.

Local Instance subG_kvΣ {Σ} : subG kv_pbΣ Σ → pbG (pb_record:=kv_record) Σ.
Proof. intros. apply subG_pbΣ. solve_inG. Qed.

Definition replica_fname := "kv.data".

Lemma kv_pb_boot :
  ∀ σconfig σsrv1 σsrv2 (g : goose_lang.global_state),
  (* *)
  ffi_initgP g.(global_world) →

  ffi_initP σconfig.(world) g.(global_world) →
  ffi_initP σsrv1.(world) g.(global_world) →
  ffi_initP σsrv2.(world) g.(global_world) →
  (*
  g.(global_world).(grove_net) !! shardId = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! coordId = Some (∅ : gset message) → *)
  grove_dist_adequate
    [ {| init_thread := config_main #() ; init_restart := of_val #(); init_local_state := σconfig |}]
    [(kv_replica_main1 #(), σsrv1); (kv_replica_main2 #(), σsrv2)] g (λ _, True).
Proof.
  intros ????.
  intros Hinitg Hinitconfig Hinitr1 Hinitr2.
  eapply (grove_ffi_dist_adequacy (kv_pbΣ)).
  { assumption. }
  { repeat constructor; naive_solver. }

  intros Hheap.
  iIntros "Hchan".
  iSplitR ""; last first.
  { iModIntro. iMod (fupd_mask_subseteq ∅); eauto. }

  (* TODO: initialize ghost state, including RPC stuff *)
  (*
    Here's the order stuff gets allocated in.
    - pb global state (includes config and epoch points tos)
    - is_host for config server
    - each replica server's ghost state
    - each replica server's ghost state
    - is_host for each pb server
    - config server state, and the is_conf_inv invariant
  *)
  (*
  eassert (pb_ghostG (EntryType:=(kv_record.(pb_OpType) * gname)) kv_pbΣ) as HghostG.
  { apply _. }
   *)

  iMod (pb_system_init) as "HH".
  iMod (pb_system_init) as (γsys) "(#Hsys & Hghost & Hpbsysinit)".

  iMod (pb_init_log γsys with "[$Hghost]") as (γlog) "[Hlog #Hloginv]".

  iMod (config_ghost_init) as (γconf) "HconfInit".
  iMod (config_server_init configHost γconf with "[]") as "#HisConf".
  { admit. }

  iModIntro.
  simpl. iSplitL "HconfInit".
  {
    iIntros (HL) "Hfiles".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iApply (idempotence_wpr with "[HconfInit] []").
    {
      instantiate (1:=λ _, True%I).
      simpl.
      iApply wp_wpc.
      wp_call.
      iDestruct "HconfInit" as "(H1 & _)".
      wp_apply (config_proof.wp_MakeServer with "[$H1]").
      iIntros (?) "#Hisconf_server".
      wp_apply (config_proof.wp_Server__Serve with "[$]").
      { iFrame "#". }
      wp_pures.
      by iModIntro.
    }
    { (* crash; there should actually be no crashes of the config server *)
      iModIntro.
      iIntros.
      iModIntro.
      admit.
    }
  }
  iSplitR.
  {
    iIntros (HL) "Hfiles".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    evar (γsrv:pb_server_names).
    iApply (idempotence_wpr with "[] []").
    { (* initialization *)
      instantiate (1:=(λ (_:heapGS kv_pbΣ), ∃ data', replica_fname f↦ data' ∗ ▷ file_crash (own_Server_ghost γsys γsrv) data')%I).
      simpl.
      iDestruct (wpc_kv_replica_main1 with "[] [Hsys]") as "HH".
      { admit. }
      { admit. }
      { admit. }
    }
    { (* recovery *)
      iModIntro.
      iIntros.
      iNext.
      rewrite /post_crash.
      iIntros.
      iModIntro.
      iSplit; first done.
      iIntros.
      iSplit; first done.
      iDestruct (wpc_kv_replica_main1 γsys γsrv with "[] [Hsys] []") as "HH".
      { admit. }
      { admit. }
      { admit. }
      iExactEq "HH".
      f_equal.
      { admit. }
      f_equal.
      unfold closed_wpcs.replica_fname.
      unfold replica_fname.
    }
  }
  (* other servers remain *)
Admitted.

Print Assumptions kv_pb_boot.

End closed.
