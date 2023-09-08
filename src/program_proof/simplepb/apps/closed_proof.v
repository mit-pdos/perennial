From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.simplepb.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi_adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.simplepb Require Import config_proof pb_definitions
     pb_protocol pb_init_proof config_protocol_proof.
From Perennial.program_proof.simplepb Require Import kv_proof admin_proof.
From Perennial.program_proof.simplepb.simplelog Require Import proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.program_proof.simplepb.apps Require Import closed_wpcs.
From Perennial.goose_lang Require Import crash_borrow crash_modality.
From Perennial.goose_lang Require Import typed_slice.

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

Definition kv_pbΣ := #[heapΣ; ekvΣ; bankΣ].

#[global]
Instance sys_inv_into_crash `{!heapGS Σ} EntryType `{!pbG Σ} γsys :
  IntoCrash (is_pb_system_invs γsys) (λ hG', @is_pb_system_invs EntryType Σ (_ hG') _ γsys)
.
Proof.
  rewrite /IntoCrash /is_pb_system_invs.
  iIntros "$". iIntros; eauto.
Qed.

(* The globalGS equality should actually always be the case (or more precisely,
 we should be unbundling, but let's include it here in the conclusion as a
 hack *)

(*
#[global]
Instance is_pb_config_host_into_crash `{hG0: !heapGS Σ} PBRecord `{!pbG Σ} u γ:
  IntoCrash (is_pb_config_hosts u γ)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_pb_config_hosts (pb_record:=PBRecord) u γ)%I
.
Proof.
  rewrite /IntoCrash /is_pb_host.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance is_proph_read_into_crash `{hG0: !heapGS Σ} PBRecord `{!pbG Σ} γ:
  IntoCrash (clerk_proof.is_proph_read_inv γ)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗
           clerk_proof.is_proph_read_inv (pb_record:=PBRecord) γ)%I
.
Proof.
  rewrite /IntoCrash /is_pb_host.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance is_kv_config_into_crash `{hG0: !heapGS Σ} `{!ekvG Σ} u γ:
  IntoCrash (is_kv_config_hosts u γ)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_kv_config_hosts u γ)%I
.
Proof.
  rewrite /IntoCrash /is_kv_config_hosts.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance is_bank_into_crash `{hG0: !heapGS Σ} `{!bankG Σ} a b c d :
  IntoCrash (is_bank a b c d)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_bank a b c d)%I
.
Proof.
  rewrite /IntoCrash /is_bank.
  iIntros "$". iIntros; eauto.
Qed.

#[global]
Instance file_crash_into_crash `{hG0: !heapGS Σ} SMRecord `{!pbG Σ} γsys γsrv1 data:
  IntoCrash (file_crash (own_Server_ghost_f γsys γsrv1) data)
    (λ hG, (file_crash (sm_record := SMRecord) (own_Server_ghost_f γsys γsrv1 ) data)).
Proof.
  rewrite /IntoCrash /file_crash.
  iIntros "$". iIntros; eauto.
Qed.
 *)

Definition kv_replica_main_crash_cond `{ekvG Σ} γsys fname γsrv1:=
(λ hG : heapGS Σ, ∃ data',
    (fname f↦ data') ∗ ▷ file_crash (own_Server_ghost_f γsys γsrv1) data')%I.

Lemma wpr_kv_replica_main fname me configHost {Σ} {HKV: ekvG Σ}
                               {HG} {HL}:
  let hG : heapGS Σ := {| goose_globalGS := HG; goose_localGS := HL |} in
  "Hinit" ∷ fname f↦[] -∗
  wpr NotStuck ⊤ (kv_replica_main #(LitString fname) #me #configHost) (kv_replica_main #(LitString fname) #me #configHost) (λ _ : goose_lang.val, True)
    (λ _ , True) (λ _ _, True).
Proof.
  Locate wpr.
  Print wpr.
   iIntros. iNamed.
   iApply (idempotence_wpr with "[Hinit Hfile_crash] []").
   {
     instantiate (1:=kv_replica_main_crash_cond γsys fname γsrv).
     simpl.
     wpc_apply (wpc_kv_replica_main γsys γsrv with "[] [$] [$] [$] [$]").
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
     iDestruct "Hinvs" as "-#Hinvs".
     iDestruct "Hsrvhost1" as "-#Hsrvhost1".
     iDestruct "Hconfhost" as "-#Hconfhost".
     iDestruct "Hproph" as "-#Hproph".
     iCrash.
     iIntros "_".
     destruct hL as [HG'' ?].
     iSplit; first done.
     iDestruct "Hsrvhost1" as "(%&Hsrvhost1)".
     iDestruct "Hconfhost" as "(%&Hconfhost)".
     iDestruct "Hproph" as "(%&Hproph)".
     subst.
     clear hG'.
     clear hL'.
     (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
     set (hG2' := HeapGS _ _ goose_localGS).
     simpl.
     wpc_apply (wpc_kv_replica_main (heapGS0:=hG2') γsys γsrv with "[] [$] [$] [$] [$]").
     { iIntros "H".
       iDestruct "H" as (?) "[Hfile Hcrash]".
       iExists _.
       iFrame.
     }
     iExists _. iFrame.
   }
Qed.

Lemma wp_lconfig_main γconf {Σ} {HKV: ekvG Σ} {HG} {HL} fname γ γsrv wf someN
      (pPwf:configParams.Pwf.t Σ) (pNtop:configParams.Ntop.t)
  :
  let initconfig := configParams.initconfig.mk [lr1Host ; lr2Host] in
  let paxosParams := definitions.mpaxosParams.mk Σ [γsrv] initstate wf someN in
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  "#Hhost" ∷ is_config_host lconfigHost γconf -∗
  "#HpaxosHost" ∷ definitions.is_mpaxos_host lconfigHostPaxos γ γsrv -∗
  WP lconfig_main #(str fname) {{ _, True }}
.
Proof.
  intros ???.
  repeat iNamed 1.
  wp_call.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (servers_ptr) "Hservers".
  wp_pures.

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite replicate_0.
  simpl.
  wp_apply wp_mk_lconfig_hosts.
  iIntros (?) "#Hhosts_sl".
  iMod (readonly_alloc_1 with "Hsl") as "Hsl".
  wp_apply (config_proof.wp_StartServer with "[Hsl]").
  {
    iFrame "Hsl". iFrame "Hhost".
    instantiate (8:=[lconfigHost]).
    iSplitR; first admit.
    iSplitR; first admit.
    iSplitR; first admit.
    iSplitR.
    { admit. } (* FIXME: parameters don't match *)
    admit.
  }
  iIntros (?) "#Hissrv".
  wp_apply (wp_Server__Serve with "[$]").
  {
    iFrame "Hissrv".
  }
  wp_pures.
  done.
Qed.

Lemma wp_dconfig_main γconf {Σ} {HKV: ekvG Σ} {HG} {HL}:
  let hG := {| goose_globalGS := HG; goose_localGS := HL |} in
  "HconfInit" ∷ makeConfigServer_pre γconf [dr1Host; dr2Host] ∗
  "#Hhost" ∷ is_config_host dconfigHost γconf -∗
  WP dconfig_main #() {{ _, True }}
.
Proof.
  intros ?.
  iNamed 1.
  wp_call.
  wp_apply (wp_NewSlice).
  iIntros (?) "Hsl".
  wp_apply wp_ref_to.
  { done. }
  iIntros (servers_ptr) "Hservers".
  wp_pures.

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  wp_apply (wp_SliceAppend with "Hsl").
  iIntros (?) "Hsl".
  wp_apply (wp_StoreAt with "[$Hservers]").
  { done. }
  iIntros "Hservers".

  wp_apply (wp_LoadAt with "[$Hservers]").
  iIntros "Hservers".
  iDestruct (own_slice_to_small with "Hsl") as "Hsl".
  rewrite replicate_0.
  simpl.
  wp_apply (config_proof.wp_MakeServer with "[$HconfInit $Hsl]").
  iIntros (?) "#Hissrv".
  wp_apply (wp_Server__Serve with "[$]").
  {
    iFrame "Hissrv".
  }
  wp_pures.
  done.
Qed.

(* There's one of these in kvee_proof.v, so I got rid of this.
   This is probably a remnant of an older version of the proof in which the subG
   wasn't proven anywhere else.
 *)
Local Instance subG_ekvΣ {Σ} : subG kv_pbΣ Σ → ekvG Σ.
Proof. intros. solve_inG. Qed.

Definition replica_fname := "kv.data".

(* FIXME: put this in the file that defines ekvΣ? *)
Opaque ekvΣ.
Lemma kv_pb_boot :
  ∀ σdconfig σdsrv1 σdsrv2
    σlconfig σlsrv1 σlsrv2
    σbt σba
    (g : goose_lang.global_state),
  (* *)
  chan_msg_bounds g.(global_world).(grove_net) →

  file_content_bounds σbt.(world).(grove_node_files) →
  file_content_bounds σba.(world).(grove_node_files) →

  file_content_bounds σdconfig.(world).(grove_node_files) →
  file_content_bounds σdsrv1.(world).(grove_node_files) →
  file_content_bounds σdsrv2.(world).(grove_node_files) →
  σdsrv1.(world).(grove_node_files) !! replica_fname = Some [] →
  σdsrv2.(world).(grove_node_files) !! replica_fname = Some [] →

  g.(global_world).(grove_net) !! dconfigHost = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! dr1Host = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! dr2Host = Some (∅ : gset message) →

  file_content_bounds σlconfig.(world).(grove_node_files) →
  file_content_bounds σlsrv1.(world).(grove_node_files) →
  file_content_bounds σlsrv2.(world).(grove_node_files) →
  σlsrv1.(world).(grove_node_files) !! replica_fname = Some [] →
  σlsrv2.(world).(grove_node_files) !! replica_fname = Some [] →

  g.(global_world).(grove_net) !! lconfigHost = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lr1Host = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lr2Host = Some (∅ : gset message) →

  grove_dist_adequate
    [ {| init_thread := dconfig_main #() ; init_restart := of_val #(); init_local_state := σdconfig |} ;
      {| init_thread := lconfig_main #() ; init_restart := of_val #(); init_local_state := σlconfig |}
      ]
    [(kv_replica_main #(LitString replica_fname) #(dr1Host:u64) #dconfigHost, σdsrv1);
     (kv_replica_main #(LitString replica_fname) #(dr2Host:u64) #dconfigHost, σdsrv2);
     (kv_replica_main #(LitString replica_fname) #(lr1Host:u64) #lconfigHost, σlsrv1);
     (kv_replica_main #(LitString replica_fname) #(lr2Host:u64) #lconfigHost, σlsrv2);

     (bank_transferer_main #(), σbt);
     (bank_auditor_main #(), σba)
    ] g (λ _, True).
Proof.
  intros ?????????.
  intros Hinitg. intros HbtChan1 HbaChan2.
  intros Hdinitconfig Hdinitr1 Hdinitr2 Hdinitr1file Hdinitr2file HdconfChan Hdr1Chan Hdr2Chan.
  intros Hlinitconfig Hlinitr1 Hlinitr2 Hlinitr1file Hlinitr2file HlconfChan Hlr1Chan Hlr2Chan.
  eapply (grove_ffi_dist_adequacy (kv_pbΣ)).
  { assumption. }
  { repeat constructor; naive_solver. }

  intros Hheap.
  iIntros "Hchan".
  iSplitR ""; last first.
  { iModIntro. iMod (fupd_mask_subseteq ∅); eauto. }

  (* SET UP RSM SYTEM *)
  (* First, pre-set up the two pairs of KV replica servers *)
  iMod (prealloc_simplepb_server) as (γsrvd1) "[#Hdsrv1wit Hdsrv1]".
  iMod (prealloc_simplepb_server) as (γsrvd2) "[#Hdsrv2wit Hdsrv2]".
  set (confdγs:=[γsrvd1 ; γsrvd2]).
  iMod (alloc_simplepb_system confdγs with "[]") as (γdpb) "Hd".
  { simpl. lia. }
  { iIntros. rewrite /confdγs elem_of_list_In /= in H.
    naive_solver. }

  iDestruct "Hd" as "(#Hinvs & Hlog & #Hwits & Hconf1 & Hconf2 & #Hclient_invs)".

  (* Now, set up the exactly-once kv system *)
  iMod (alloc_ekv _ {[ "init"; "a1"; "a2" ]} with "Hlog") as (?) "[#Hclient_invs2 Hkvs]".

  (* Now, set up all the hosts *)
  iDestruct (big_sepM_delete with "Hchan") as "[HconfChan Hchan]".
  { apply HdconfChan. } (* get out conf chan points-to for later *)

  iDestruct (big_sepM_delete with "Hchan") as "[Hr1Chan Hchan]".
  { rewrite lookup_delete_Some. split; last apply Hdr1Chan. done. }
  iMod (pb_host_init dr1Host with "Hr1Chan") as "#Hsrvhost1".

  iDestruct (big_sepM_delete with "Hchan") as "[Hr2Chan Hchan]".
  { rewrite lookup_delete_Some.
    rewrite lookup_delete_Some.
    split; last (split ; last apply Hdr2Chan); done. }
  iMod (pb_host_init dr2Host with "Hr2Chan") as "#Hsrvhost2".

  set (dconf:=[dr1Host ; dr2Host]).
  iMod (alloc_pb_config_ghost γdpb dconf confdγs with "[] Hconf1 Hconf2") as (γconf) "[#Hconf HconfInit]".
  {
    iFrame "#".
    by iApply big_sepL2_nil.
  }

  iMod (config_server_init dconfigHost γconf with "HconfChan") as "#Hconfhost".

  iAssert (is_pb_config_host dconfigHost γdpb) with "[]" as "#HbConfHost".
  { iExists _. iFrame "#". }
  (* END SET UP RSM SYTEM *)
  (* TODO: the above should probably be a lemma *)

  (* SET UP RSM SYTEM *)
  (* First, pre-set up the two pairs of KV replica servers *)
  iMod (prealloc_simplepb_server) as (γsrvl1) "[#Hlsrv1wit Hlsrv1]".
  iMod (prealloc_simplepb_server) as (γsrvl2) "[#Hlsrv2wit Hlsrv2]".
  set (conflγs:=[γsrvl1 ; γsrvl2]).
  iMod (alloc_simplepb_system conflγs with "[]") as (γlpb) "Hl".
  { simpl. lia. }
  { iIntros. rewrite /conflγs elem_of_list_In /= in H.
    naive_solver. }

  iDestruct "Hl" as "(#Hlinvs & Hllog & #Hlwits & Hlconf1 & Hlconf2 & #Hlclient_invs)".

  (* Now, set up the exactly-once kv system *)
  iMod (alloc_ekv _ {[ "init"; "a1"; "a2" ]} with "Hllog") as (?) "[#Hlclient_invs2 Hlkvs]".

  (* Now, set up all the hosts *)
  iDestruct (big_sepM_delete with "Hchan") as "[HlconfChan Hchan]".
  { repeat rewrite lookup_delete_Some.
    split_and!; last apply HlconfChan; done. }

  iDestruct (big_sepM_delete with "Hchan") as "[Hlr1Chan Hchan]".
  { repeat rewrite lookup_delete_Some. split_and!; last apply Hlr1Chan; done. }
  iMod (pb_host_init lr1Host with "Hlr1Chan") as "#Hlsrvhost1".

  iDestruct (big_sepM_delete with "Hchan") as "[Hlr2Chan Hchan]".
  { repeat rewrite lookup_delete_Some.
    split_and!; last apply Hlr2Chan; done. }
  iMod (pb_host_init lr2Host with "Hlr2Chan") as "#Hlsrvhost2".

  set (lconf:=[lr1Host ; lr2Host]).
  iMod (alloc_pb_config_ghost γlpb lconf conflγs with "[] Hlconf1 Hlconf2") as (γlconf) "[#Hlconf HlconfInit]".
  {
    iFrame "#".
    by iApply big_sepL2_nil.
  }

  iMod (config_server_init lconfigHost γlconf with "HlconfChan") as "#Hlconfhost".

  iAssert (is_pb_config_host lconfigHost γlpb) with "[]" as "#HlConfHost".
  { iExists _. iFrame "#". }
  (* END SET UP RSM SYTEM *)

  (* set up bank *)
  iAssert (|={⊤}=> is_bank "init" _ _ {[ "a1" ; "a2" ]})%I with "[Hlkvs Hkvs]" as ">#Hbank".
  {
    iDestruct (big_sepS_delete _ _ "init" with "Hlkvs") as "(Hinit&Hlkvs)".
    { set_solver. }
    instantiate (2:=Build_lock_names (kv_ptsto γkv0)).
    rewrite /is_bank.
    iMod (lock_alloc lockN {| kvptsto_lock := kv_ptsto γkv0 |} _ "init" with "[Hinit] [-]") as "$"; last done.
    { iFrame. }
    iDestruct (big_sepS_delete _ _ "init" with "Hkvs") as "(Hinit&Hkvs)".
    { set_solver. }
    iLeft.
    instantiate (1:=kv_ptsto γkv).
    iFrame.
    iApply (big_sepS_sep).
    eassert (_ ∖ _ = {[ "a1"; "a2" ]}) as ->.
    { set_solver. }
    iFrame.
  }

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
      iApply (wp_dconfig_main _ with "[$]").
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
  iSplitL "HlconfInit".
  {
    iIntros (HL) "Hfiles".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _). (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
    iApply (idempotence_wpr with "[HlconfInit] []").
    {
      instantiate (1:=λ _, True%I).
      simpl.
      iApply wp_wpc.
      iApply (wp_lconfig_main _ with "[$]").
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
  iSplitL "Hdsrv1".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iSpecialize ("Hdsrv1" $! γdpb with "[]").
    { iApply "Hwits". iPureIntro. rewrite /confdγs elem_of_list_In /= //. naive_solver. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iAssert (file_crash (own_Server_ghost_f γdpb _) []) with "[Hdsrv1]" as "HfileCrash".
    { iLeft. by iFrame. }
    iApply (@wpr_kv_replica_main _ _ _ γdpb γsrvd1 with "[$] [$] [$] [$] [$]").
  }
  (* TODO: do like above for replica main1 as separate lemma *)
  iSplitL "Hdsrv2".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iSpecialize ("Hdsrv2" $! γdpb with "[]").
    { iApply "Hwits". iPureIntro. rewrite /confdγs elem_of_list_In /= //. naive_solver. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iAssert (file_crash (own_Server_ghost_f γdpb _) []) with "[Hdsrv2]" as "HfileCrash".
    { iLeft. by iFrame. }
    iApply (@wpr_kv_replica_main _ _ _ γdpb γsrvd2 with "[$] [$] [$] [$] [$]").
  }
  iSplitL "Hlsrv1".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iSpecialize ("Hlsrv1" $! γlpb with "[]").
    { iApply "Hlwits". iPureIntro. rewrite /confdγs elem_of_list_In /= //. naive_solver. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iAssert (file_crash (own_Server_ghost_f γlpb _) []) with "[Hlsrv1]" as "HfileCrash".
    { iLeft. by iFrame. }
    iApply (@wpr_kv_replica_main _ _ _ γlpb γsrvl1 with "[$] [$] [$] [$] [$]").
  }
  iSplitL "Hlsrv2".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iSpecialize ("Hlsrv2" $! γlpb with "[]").
    { iApply "Hlwits". iPureIntro. rewrite /confdγs elem_of_list_In /= //. naive_solver. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iAssert (file_crash (own_Server_ghost_f γlpb _) []) with "[Hlsrv2]" as "HfileCrash".
    { iLeft. by iFrame. }
    iApply (@wpr_kv_replica_main _ _ _ γlpb γsrvl2 with "[$] [$] [$] [$] [$]").
  }
  iAssert (is_kv_config dconfigHost γkv) with "[]" as "#Hkvconf".
  {
    iDestruct "Hclient_invs2" as (??) "H".
    repeat iExists _.
    iDestruct "H" as "( $ & $ & $ )".
    iFrame "#".
  }
  iAssert (is_kv_config lconfigHost γkv0) with "[]" as "#Hlkvconf".
  {
    iDestruct "Hlclient_invs2" as (??) "H".
    repeat iExists _.
    iDestruct "H" as "( $ & $ & $ )".
    iFrame "#".
  }
  iSplitR.
  {
    iIntros (HL) "Hfiles".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iApply (idempotence_wpr with "[] []").
    { instantiate (1:=(λ _, True)%I). simpl.
      iApply wp_wpc.
      wp_apply (wp_bank_transferer_main with "[]"); last done.
      repeat iExists _.
      iFrame "Hbank #".
    }
    {
      rewrite /hG'.
      clear hG'.
      iModIntro.
      iIntros (????) "_".
      iNext.
      simpl.
      set (hG' := HeapGS _ _ hL').
      iDestruct "Hinvs" as "-#Hinvs".
      iDestruct "Hkvconf" as "-#Hkvconf".
      iDestruct "Hlkvconf" as "-#Hlkvconf".
      iDestruct "Hbank" as "-#Hbank".
      iCrash.
      iIntros "$".
      destruct hL as [HG'' ?].
      iDestruct "Hkvconf" as "[%Hheap2 #Hkvconf]"; subst.
      iDestruct "Hlkvconf" as "[_ #Hlkvconf]".
      iDestruct "Hbank" as "[_ #Hbank]".
      clear hG'.
      clear hL'.
      (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      set (hG2' := HeapGS _ _ goose_localGS).
      simpl.
      iApply wp_wpc.
      wp_apply (wp_bank_transferer_main with "[]"); last done.
      repeat iExists _.
      iFrame "Hbank #".
    }
  }
  iSplitR.
  {
    iIntros (HL) "Hfiles".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iApply (idempotence_wpr with "[] []").
    { instantiate (1:=(λ _, True)%I). simpl.
      iApply wp_wpc.
      wp_apply (wp_bank_auditor_main with "[]"); last done.
      repeat iExists _.
      iFrame "Hbank #".
    }
    {
      rewrite /hG'.
      clear hG'.
      iModIntro.
      iIntros (????) "_".
      iNext.
      simpl.
      set (hG' := HeapGS _ _ hL').
      iDestruct "Hinvs" as "-#Hinvs".
      iDestruct "Hkvconf" as "-#Hkvconf".
      iDestruct "Hlkvconf" as "-#Hlkvconf".
      iDestruct "Hbank" as "-#Hbank".
      iCrash.
      iIntros "$".
      destruct hL as [HG'' ?].
      iDestruct "Hkvconf" as "[%Hheap2 #Hkvconf]"; subst.
      iDestruct "Hlkvconf" as "[_ #Hlkvconf]".
      iDestruct "Hbank" as "[_ #Hbank]".
      clear hG'.
      clear hL'.
      (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      set (hG2' := HeapGS _ _ goose_localGS).
      simpl.
      iApply wp_wpc.
      wp_apply (wp_bank_auditor_main with "[]"); last done.
      repeat iExists _.
      iFrame "Hbank #".
    }
  }
  done.
Qed.

End closed.
