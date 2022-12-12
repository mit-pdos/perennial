From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.simplepb Require Import config_proof pb_definitions pb_ghost pb_init_proof.
From Perennial.program_proof.simplepb Require Import kv_proof admin_proof.
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

Definition kv_pbΣ := #[heapΣ; kv64Σ].

Definition configHost : chan := U64 10.
Definition r1Host: chan := U64 1.
Definition r2Host: chan := U64 2.

#[global]
Instance sys_inv_into_crash `{!heapGS Σ} EntryType `{!pb_ghostG Σ} γsys :
  IntoCrash (sys_inv γsys) (λ hG', @sys_inv EntryType Σ (_ hG') _ γsys)
.
Proof.
  rewrite /IntoCrash /sys_inv.
  iIntros "$". iIntros; eauto.
Qed.

(* The globalGS equality should actually always be the case (or more precisely, we should be unbundling,
 but let's include it here in the conclusion as a hack *)
#[global]
Instance is_pb_host_into_crash `{hG0: !heapGS Σ} PBRecord `{!pbG Σ} u γ1 γ2 :
  IntoCrash (is_pb_host u γ1 γ2)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_pb_host (pb_record:=PBRecord) u γ1 γ2)%I
.
Proof.
  rewrite /IntoCrash /is_pb_host.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance file_crash_into_crash `{hG0: !heapGS Σ} SMRecord `{!pbG Σ} γsys γsrv1 data:
  IntoCrash (file_crash (own_Server_ghost γsys γsrv1 ) data)
    (λ hG, (file_crash (sm_record := SMRecord) (own_Server_ghost γsys γsrv1 ) data)).
Proof.
  rewrite /IntoCrash /file_crash.
  iIntros "$". iIntros; eauto.
Qed.

Definition kv_replica_main1_crash_cond `{kv64G Σ} γsys replica_fname γsrv1:=
(λ hG : heapGS Σ, ∃ data', (replica_fname f↦ data') ∗ ▷ file_crash (own_Server_ghost γsys γsrv1) data')%I.

Lemma wpr_kv_replica_main1 γsys γlog γsrv1 γconf γkv {Σ} {HKV: kv64G Σ}
                               {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  "Hinv" ∷ is_inv γlog γsys -∗
  "Hsys" ∷ sys_inv γsys -∗
  "Hkvinv" ∷ kv_inv γlog γkv -∗
  "Hprop_lb" ∷ is_proposal_lb γsys 0%Z [] -∗
  "Hprop_facts" ∷ is_proposal_facts γsys 0%Z [] -∗
  "Hconf" ∷ is_conf_inv γsys γconf -∗
  "Hconfhost" ∷ is_host configHost γconf -∗
  "Hsrvhost1" ∷ is_pb_host r1Host γsys γsrv1 -∗
  "Hinit" ∷ replica_fname f↦[] -∗
  "Hfile_crash" ∷ file_crash (own_Server_ghost γsys γsrv1) [] -∗
  wpr NotStuck ⊤ (kv_replica_main1 #()) (kv_replica_main1 #()) (λ _ : goose_lang.val, True)
    (λ _ , True) (λ _ _, True).
Proof.
   iIntros. iNamed.
   iApply (idempotence_wpr with "[Hinit Hfile_crash] []").
   {
     instantiate (1:=kv_replica_main1_crash_cond γsys replica_fname γsrv1).
     simpl.
     wpc_apply (wpc_kv_replica_main1 γsys γsrv1 with "[] [$Hsrvhost1] [$Hsys]").
     { iIntros "$". }
     iExists _. iFrame.
   }
   { (* recovery *)
     rewrite /hG.
     clear hG.
     iModIntro.
     iIntros (????) "Hcrash".
     iNext.
     iDestruct "Hcrash" as (?) "[Hfile Hcrash]".
     simpl.
     set (hG' := HeapGS _ _ hL').
     iDestruct "Hsys" as "-#Hsys".
     iDestruct "Hsrvhost1" as "-#Hsrvhost1".
     iCrash.
     iIntros "_".
     destruct hL as [HG'' ?].
     iSplit; first done.
     iDestruct "Hsrvhost1" as "(%Heq&Hsrvhost1)".
     subst.
     clear hG'.
     clear hL'.
     (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
     set (hG2' := HeapGS _ _ goose_localGS).
     simpl.
     wpc_apply (wpc_kv_replica_main1 (heapGS0:=hG2') γsys γsrv1 with "[] [$Hsrvhost1] [$Hsys]").
     { iIntros "H".
       iDestruct "H" as (?) "[Hfile Hcrash]".
       iExists _.
       iFrame.
     }
     iExists _. iFrame.
   }
Qed.

Local Instance subG_kv64Σ {Σ} : subG kv_pbΣ Σ → kv64G Σ.
Proof. intros. solve_inG. Qed.

Definition replica_fname := "kv.data".


Lemma kv_pb_boot :
  ∀ σconfig σsrv1 σsrv2 (g : goose_lang.global_state),
  (* *)
  ffi_initgP g.(global_world) →

  ffi_initP σconfig.(world) g.(global_world) →
  ffi_initP σsrv1.(world) g.(global_world) →
  ffi_initP σsrv2.(world) g.(global_world) →

  σsrv1.(world).(grove_node_files) !! replica_fname = Some [] →
  σsrv2.(world).(grove_node_files) !! replica_fname = Some [] →

  g.(global_world).(grove_net) !! configHost = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! r1Host = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! r2Host = Some (∅ : gset message) →
  grove_dist_adequate
    [ {| init_thread := config_main #() ; init_restart := of_val #(); init_local_state := σconfig |}]
    [(kv_replica_main1 #(), σsrv1); (kv_replica_main2 #(), σsrv2)] g (λ _, True).
Proof.
  intros ????.
  intros Hinitg Hinitconfig Hinitr1 Hinitr2 Hinitr1file Hinitr2file HconfChan Hr1Chan Hr2Chan.
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
  iMod (kv_system_init) as (???) "(Hconfinit & #Hinv & #Hsys & #Hkvinv & #Hprop_lb & #Hprop_facts)".
  iMod (config_ghost_init_2 γsys with "Hconfinit") as (γconf) "[#Hconf HconfInit]".

  iDestruct (big_sepM_delete with "Hchan") as "[HconfChan Hchan]".
  { apply HconfChan. }

  iMod (config_server_init configHost γconf with "HconfChan") as "#Hconfhost".

  iMod (pb_server_init with "Hprop_lb Hprop_facts") as (γsrv1) "Hsrv1".
  iMod (pb_server_init with "Hprop_lb Hprop_facts") as (γsrv2) "Hsrv2".

  iDestruct (big_sepM_delete with "Hchan") as "[Hr1Chan Hchan]".
  { rewrite lookup_delete_Some. split; last apply Hr1Chan. done. }
  iMod (pb_host_init r1Host with "Hr1Chan") as "#Hsrvhost1".

  iDestruct (big_sepM_delete with "Hchan") as "[Hr2Chan Hchan]".
  { rewrite lookup_delete_Some.
    rewrite lookup_delete_Some.
    split; last (split ; last apply Hr2Chan); done. }
  iMod (pb_host_init r2Host with "Hr2Chan") as "#Hsrvhost2".

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
      wp_apply (config_proof.wp_MakeServer with "HconfInit").
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
      rewrite /post_crash.
      iIntros. iModIntro.
      iSplit; first done. iIntros. iSplit; first done.
      set (hG2' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      wpc_pures.
      { done. }
      done.
    }
  }
  iSplitL "Hsrv1".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iMod (kv_server_init with "[$Hsrv1 $HH]") as "Hinit".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iDestruct "Hinit" as "(?&?)".
    iApply (@wpr_kv_replica_main1 with "[$] [$] [$] [$] [$] [$] [$] [$] [$] [$]").
  }
  (* TODO: do like above for replica main1 as separate lemma *)
  iSplitL "Hsrv2".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iMod (kv_server_init with "[$Hsrv2 $HH]") as "Hinit".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iApply (idempotence_wpr with "[Hinit] []").
    { (* initialization *)
      instantiate (1:= (λ (hG:heapGS kv_pbΣ), ∃ data',
            (gen_heap.mapsto (hG:=(@groveG_files_heapG kv_pbΣ (@goose_groveNodeGS kv_pbΣ hG.(goose_localGS) ))) replica_fname (DfracOwn (1)) data') ∗
            ▷ file_crash (own_Server_ghost γsys γsrv2) data')%I).
      simpl.
      wpc_apply (wpc_kv_replica_main2 γsys γsrv2 with "[] [$Hsrvhost2] [$Hsys]").
      { iIntros "$". }
      iExists _. iFrame.
    }
    { (* recovery *)
      iModIntro.
      iIntros (????) "Hcrash".
      iNext.
      iDestruct "Hcrash" as (?) "[Hfile Hcrash]".
      iDestruct (file_pointsto_post_crash with "Hfile") as "Hfile".
      rewrite /post_crash.
      iIntros. iModIntro.
      iSplit; first done. iIntros. iSplit; first done.
      iMod ("Hfile" $! _ _ _ _) as "[_ Hfile]".
      set (hG2' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      wpc_apply (wpc_kv_replica_main2 γsys γsrv2 with "[] [$Hsrvhost2] [$Hsys]").
      { iIntros "H".
        iDestruct "H" as (?) "[Hfile Hcrash]".
        iExists _.
        iFrame.
      }
      iExists _. iFrame.
    }
  }
  done.
  Unshelve.
  { done. }
  { done. }
  { split; last done. simpl. admit. }
Admitted.

Print Assumptions kv_pb_boot.

End closed.
