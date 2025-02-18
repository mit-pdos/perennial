From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.gokv.vrsm.apps Require Import closed.

From Perennial.goose_lang Require adequacy dist_adequacy.
From Perennial.goose_lang.ffi Require grove_ffi.adequacy.
From Perennial.program_logic Require dist_lang.

From Perennial.program_proof.vrsm Require Import config_proof replica.definitions
     protocol replica.init_proof config_protocol_proof storage.proof closed_wpcs.
From Perennial.program_proof.vrsm Require Import kv_proof reconfig.proof.
From Perennial.program_proof.grove_shared Require Import urpc_proof.
From Perennial.goose_lang Require Import crash_borrow crash_modality.
From Perennial.goose_lang Require Import typed_slice.

Module closed.

Import goose_lang.adequacy dist_adequacy grove_ffi.adequacy dist_lang.

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

#[global]
Instance is_bank_into_crash `{hG0: !heapGS Σ} `{!bankG Σ} a b c d :
  IntoCrash (is_bank a b c d)
    (λ hG, ⌜ hG0.(goose_globalGS) = hG.(goose_globalGS) ⌝ ∗ is_bank a b c d)%I
.
Proof.
  rewrite /IntoCrash /is_bank.
  iIntros "$". iIntros; eauto.
Qed.

(* There's one of these in kvee_proof.v, so I got rid of this.
   This is probably a remnant of an older version of the proof in which the subG
   wasn't proven anywhere else.
 *)
Local Instance subG_ekvΣ {Σ} : subG kv_pbΣ Σ → ekvG Σ.
Proof. intros. solve_inG. Qed.

Definition replica_fname := "kv.data"%go.

(* FIXME: put this in the file that defines ekvΣ? *)
Opaque ekvΣ.
Lemma closed_bank :
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
  σdconfig.(world).(grove_node_files) !! replica_fname = Some [] →

  g.(global_world).(grove_net) !! dconfigHost = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! dconfigHostPaxos = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! dr1Host = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! dr2Host = Some (∅ : gset message) →

  file_content_bounds σlconfig.(world).(grove_node_files) →
  file_content_bounds σlsrv1.(world).(grove_node_files) →
  file_content_bounds σlsrv2.(world).(grove_node_files) →
  σlsrv1.(world).(grove_node_files) !! replica_fname = Some [] →
  σlsrv2.(world).(grove_node_files) !! replica_fname = Some [] →
  σlconfig.(world).(grove_node_files) !! replica_fname = Some [] →

  g.(global_world).(grove_net) !! lconfigHost = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lconfigHostPaxos = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lr1Host = Some (∅ : gset message) →
  g.(global_world).(grove_net) !! lr2Host = Some (∅ : gset message) →

  grove_dist_adequate
    []
    [
      (dconfig_main #(LitString replica_fname), σdconfig);
      (lconfig_main #(LitString replica_fname), σlconfig);
      (kv_replica_main #(LitString replica_fname) #(dr1Host:u64) #dconfigHost, σdsrv1);
      (kv_replica_main #(LitString replica_fname) #(dr2Host:u64) #dconfigHost, σdsrv2);
      (kv_replica_main #(LitString replica_fname) #(lr1Host:u64) #lconfigHost, σlsrv1);
      (kv_replica_main #(LitString replica_fname) #(lr2Host:u64) #lconfigHost, σlsrv2);

     (bank_transferer_main #(), σbt);
     (bank_auditor_main #(), σba)
    ] g (λ _, True).
Proof.
  intros ?????????.
  intros Hinitg. intros HbtChan1 HbaChan2.
  intros.
  (* intros Hdinitconfig Hdinitr1 Hdinitr2 Hdinitr1file Hdinitr2file HdconfChan Hdr1Chan Hdr2Chan.
  intros Hlinitconfig Hlinitr1 Hlinitr2 Hlinitr1file Hlinitr2file HlconfChan Hlr1Chan Hlr2Chan. *)
  eapply (grove_ffi_dist_adequacy (kv_pbΣ)).
  { assumption. }
  { repeat constructor; naive_solver. }

  intros Hheap.
  iIntros "Hchan".
  iSplitR ""; last first.
  { iModIntro. iMod (fupd_mask_subseteq ∅); eauto. }

  (* Allocate a vkv system *)

  set (own_chans:=(λ l, [∗ list] h ∈ l, h c↦ ∅)%I).
  iAssert (
      own_chans [dr1Host ; dr2Host] ∗
      own_chans [dconfigHost; dconfigHostPaxos] ∗
      own_chans [lr1Host ; lr2Host] ∗
      own_chans [lconfigHost; lconfigHostPaxos]
          )%I with "[Hchan]" as "Hchans".
  {
    rewrite /own_chans.
    repeat rewrite -big_sepL_app; simpl.
    repeat (
        iDestruct (big_sepM_delete with "Hchan") as "[$ Hchan]";
        first (repeat rewrite lookup_delete_Some; try split_and!; try done)
      ).
  }

  iDestruct "Hchans" as "(Hd1 & Hd2 & Hl1 & Hl2)".

  (* Allocate the kv system used for storing data *)
  iMod (alloc_vkv (ekvParams.mk [dr1Host ; dr2Host ]) [(dconfigHost, dconfigHostPaxos)]
                  {[ "init"; "a1"; "a2" ]}%go with "[Hd1 Hd2]") as "[Hdkv Hdconf]"; try (simpl; lia).
  {
    rewrite /own_chans /=.
    repeat iDestruct (wand_refl (_ ∗ _) with "[$]") as "[? ?]".
    iFrame.
  }
  iDestruct "Hdkv" as (γd)  "(Hkvs & #Hdhost & Hdsrvs)".
  iSimpl in "Hdhost".

  (* Allocate the kv system used as a lockservice *)
  iMod (alloc_vkv (ekvParams.mk [lr1Host ; lr2Host ]) [(lconfigHost, lconfigHostPaxos)]
                  {[ "init"; "a1"; "a2" ]}%go with "[Hl1 Hl2]") as "[Hlkv Hlconf]"; try (simpl; lia).
  {
    rewrite /own_chans /=.
    repeat iDestruct (wand_refl (_ ∗ _) with "[$]") as "[? ?]".
    iFrame.
  }
  iDestruct "Hlkv" as (γl)  "(Hlkvs & #Hlhost & Hlsrvs)".
  iSimpl in "Hlhost".

  (* set up bank *)
  iAssert (|={⊤}=> is_bank "init"%go _ _ {[ "a1"%go ; "a2"%go ]})%I with "[Hlkvs Hkvs]" as ">#Hbank".
  {
    iDestruct (big_sepS_delete _ _ "init"%go with "Hlkvs") as "(Hinit&Hlkvs)".
    { set_solver. }
    instantiate (2:=Build_lock_names (kv_ptsto γl)).
    rewrite /is_bank.
    iMod (lock_alloc lockN {| kvptsto_lock := kv_ptsto γl |} _ "init" with "[Hinit] [-]") as "$"; last done.
    { iFrame. }
    iDestruct (big_sepS_delete _ _ "init"%go with "Hkvs") as "(Hinit&Hkvs)".
    { set_solver. }
    iLeft.
    instantiate (1:=kv_ptsto γd).
    iFrame.
    iApply (big_sepS_sep).
    eassert (_ ∖ _ = {[ "a1"; "a2" ]}%go) as ->.
    { set_solver. }
    iFrame.
  }

  iModIntro.
  simpl.
  (* data config *)
  iDestruct "Hdconf" as "[Hdconf _]".
  iSplitL "Hdconf".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[Hfile _]".
    { done. }
    iDestruct "Hdconf" as (???) "(% & #Hhost & #Hpeers & #Hwf & Hcrash)".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    by iApply (wpr_dconfig_main with "[$]").
  }

  (* lock config *)
  iDestruct "Hlconf" as "[Hlconf _]".
  iSplitL "Hlconf".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[Hfile _]".
    { done. }
    iDestruct "Hlconf" as (???) "(% & #Hhost & #Hpeers & #Hwf & Hcrash)".
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    by iApply (wpr_lconfig_main with "[$]").
  }
  iDestruct ("Hdsrvs") as "[Hdsrv Hdsrvs]".
  iSplitL "Hdsrv".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iDestruct "Hdsrv" as (?) "[H1 H2]".
    iApply (wpr_kv_replica_main with "[- $H1]").
    { iFrame "∗#". }
  }
  iDestruct ("Hdsrvs") as "[Hdsrv Hdsrvs]".
  iSplitL "Hdsrv".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iDestruct "Hdsrv" as (?) "[H1 H2]".
    iApply (wpr_kv_replica_main with "[- $H1]").
    { iFrame "∗#". }
  }
  iDestruct ("Hlsrvs") as "[Hlsrv Hlsrvs]".
  iSplitL "Hlsrv".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iDestruct "Hlsrv" as (?) "[H1 H2]".
    iApply (wpr_kv_replica_main with "[- $H1]").
    { iFrame "∗#". }
  }
  iDestruct ("Hlsrvs") as "[Hlsrv Hlsrvs]".
  iSplitL "Hlsrv".
  {
    iIntros (HL) "Hfiles".
    iDestruct (big_sepM_lookup_acc with "Hfiles") as "[HH _]".
    { done. }
    iModIntro.
    iExists (λ _, True%I), (λ _, True%I), (λ _ _, True%I).
    set (hG' := HeapGS _ _ _).
    iDestruct "Hlsrv" as (?) "[H1 H2]".
    iApply (wpr_kv_replica_main with "[- $H1]").
    { iFrame "∗#". }
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
      iFrame "Hbank".
      iSplit. - iExact "Hdhost". - iExact "Hlhost".
    }
    {
      rewrite /hG'.
      clear hG'.
      iModIntro.
      iIntros (????) "_".
      iNext.
      simpl.
      set (hG' := HeapGS _ _ hL').
      iDestruct "Hdhost" as "-#Hdhost".
      iDestruct "Hlhost" as "-#Hlhost".
      iDestruct "Hbank" as "-#Hbank".
      iCrash.
      iIntros "$".
      destruct hL as [HG'' ?].
      set (to_name := (λ x, match x with INamed y => y | _ => "?" end)).
      repeat iSelect (⌜ _ ⌝ ∗ _)%I
             (fun H => let x := (eval compute in ("[% " +:+ to_name H +:+ "]")) in
                    iDestruct H as x).
      clear hG' hL' HL.
      subst.
      (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      set (hG2' := HeapGS _ _ goose_localGS).
      clear to_name.
      iApply wp_wpc.
      wp_apply (wp_bank_transferer_main with "[-]"); last done.
      repeat iExists _.
      iFrame "Hbank".
      iSplit. - iExact "Hdhost". - iExact "Hlhost".
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
      iFrame "Hbank".
      iSplit. - iExact "Hdhost". - iExact "Hlhost".
    }
    {
      rewrite /hG'.
      clear hG'.
      iModIntro.
      iIntros (????) "_".
      iNext.
      simpl.
      set (hG' := HeapGS _ _ hL').
      iDestruct "Hdhost" as "-#Hdhost".
      iDestruct "Hlhost" as "-#Hlhost".
      iDestruct "Hbank" as "-#Hbank".
      iCrash.
      iIntros "$".
      destruct hL as [HG'' ?].
      set (to_name := (λ x, match x with INamed y => y | _ => "?" end)).
      repeat iSelect (⌜ _ ⌝ ∗ _)%I
             (fun H => let x := (eval compute in ("[% " +:+ to_name H +:+ "]")) in
                    iDestruct H as x).
      clear hG' hL' HL.
      subst.
      (* overcome impedence mismatch between heapGS (bundled) and gooseGLobalGS+gooseLocalGS (split) proofs *)
      set (hG2' := HeapGS _ _ goose_localGS).
      clear to_name.
      iApply wp_wpc.
      wp_apply (wp_bank_auditor_main with "[-]"); last done.
      repeat iExists _.
      iFrame "Hbank".
      iSplit. - iExact "Hdhost". - iExact "Hlhost".
    }
  }
  done.
Qed.

End closed.
