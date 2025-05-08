From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import alicebob.

From Perennial.program_proof.pav Require Import
  advrpc alicebob_helpers core client client_hist cryptoffi
  get_agreement msv phys_hist rpc serde.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import waitgroup.

Notation alice_uid := (W64 0) (only parsing).
Notation bob_uid := (W64 1) (only parsing).

Section proof.
Context `{!heapGS Σ, !pavG Σ, !waitGroupG Σ}.

Definition own_alice ptr cli_γ serv (serv_good : bool) : iProp Σ :=
  ∃ (ptr_cli : loc) sl_hist epochs puts next_epoch,
  "#Hptr_serv_good" ∷ ptr ↦[alice :: "servGood"]□ #serv_good ∗
  "#Hptr_cli" ∷ ptr ↦[alice :: "cli"]□ #ptr_cli ∗
  "Hptr_hist" ∷ ptr ↦[alice :: "hist"] (slice_val sl_hist) ∗

  "Hown_cli" ∷ ClientHist.own ptr_cli (ClientHist.mk cli_γ alice_uid
    epochs puts next_epoch serv serv_good) ∗
  "Hown_hist" ∷ own_hist sl_hist puts.

Definition own_bob ptr cli_γ serv (serv_good : bool) (is_run : bool)
    (is_reg : bool) (ep : w64) (alice_pk : list w8) : iProp Σ :=
  ∃ (ptr_cli : loc) sl_alicePk next_ver,
  "#Hptr_serv_good" ∷ ptr ↦[bob :: "servGood"]□ #serv_good ∗
  "#Hptr_cli" ∷ ptr ↦[bob :: "cli"]□ #ptr_cli ∗
  "Hptr_epoch" ∷ ptr ↦[bob :: "epoch"] #ep ∗
  "Hptr_isReg" ∷ ptr ↦[bob :: "isReg"] #is_reg ∗
  "Hptr_alicePk" ∷ ptr ↦[bob :: "alicePk"] (slice_val sl_alicePk) ∗

  "Hown_cli" ∷ client.Client.own ptr_cli (client.Client.mk cli_γ
    bob_uid next_ver (if is_run then word.add ep (W64 1) else W64 0)
    serv serv_good) ∗
  "Hsl_alicePk" ∷ own_slice_small sl_alicePk byteT (DfracOwn 1) alice_pk.

Definition bob_post cli_γ vrf_pk (is_reg : bool) ep alice_pk : iProp Σ :=
  if is_reg
  then
    "#His_get_post" ∷ is_get_post_Some cli_γ vrf_pk alice_uid ep alice_pk
  else
    "#His_get_post" ∷ is_get_post_None cli_γ vrf_pk alice_uid ep.

Lemma wp_checkServErr serv_good err :
  {{{
    "%Hgenie" ∷ ⌜ serv_good = true → err = false ⌝
  }}}
  checkServErr #serv_good #err
  {{{
    RET #();
    "%Herr" ∷ ⌜ err = false ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H".
  wp_if_destruct.
  - opose proof (Hgenie _) as ->; [done|].
    wp_apply wp_Assert_true.
    wp_pures. by iApply "HΦ".
  - wp_apply wp_Assume. iIntros (?).
    destruct err; [done|].
    wp_pures. by iApply "HΦ".
Qed.

Lemma wp_alice__run ptr cli_γ serv serv_good :
  {{{
    "Hown_al" ∷ own_alice ptr cli_γ serv serv_good
  }}}
  alice__run #ptr
  {{{
    RET #();
    "Hown_al" ∷ own_alice ptr cli_γ serv serv_good
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". rewrite /alice__run.
  wp_apply wp_ref_to; [val_ty|]. iIntros "* Hptr_i".
  wp_apply (wp_forUpto
    (λ _, own_alice ptr cli_γ serv serv_good)%I
    with "[] [$Hown_al $Hptr_i]"); [word|..].
  2: { iIntros "[Hal _]". wp_pures. by iApply "HΦ". }
  clear. iIntros (? Φ) "!> H HΦ". iDestruct "H" as "((%&%&Hown_al)&Hptr_i&%)".
  wp_apply wp_Sleep.
  wp_apply (wp_SliceSingleton _ _ _ (W8 1)).
  iIntros (?) "Hsl_pk".
  iNamed "Hown_al". wp_loadField.
  iDestruct (own_slice_to_small with "Hsl_pk") as "Hsl_pk".
  wp_apply (wp_ClientHist__Put with "[$Hown_cli $Hsl_pk]").
  iIntros "* H". iNamed "H". simpl in *. wp_pures.

  iNamed "Hown_err". do 2 wp_loadField.
  wp_apply (wp_checkServErr with "[//]").
  iIntros (->).
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hptr_e".
  wp_loadField.
  iPersist "Hptr_e Hsl_pk".
  wp_apply (wp_put_hist with "[$Hown_hist]").
  { iDestruct (struct_fields_split with "Hptr_e") as "H".
    iNamed "H". iFrame "#". }
  iIntros "*". iNamed 1.
  wp_storeField.
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_bob__run ptr cli_γ serv serv_good a0 a1 a2 :
  {{{
    "Hown_bob" ∷ own_bob ptr cli_γ serv serv_good false a0 a1 a2
  }}}
  bob__run #ptr
  {{{
    ep is_reg alice_pk, RET #();
    "Hown_bob" ∷ own_bob ptr cli_γ serv serv_good true is_reg ep alice_pk ∗
    "#Hbob_post" ∷ bob_post cli_γ serv.(server.Server.vrf_pk) is_reg ep alice_pk
  }}}.
Proof.
  iIntros (Φ) "H HΦ". wp_rec.
  iNamed "H". iNamed "Hown_bob". iClear "Hsl_alicePk".
  wp_apply wp_Sleep. wp_loadField.
  wp_apply (wp_Client__Get with "Hown_cli"). simpl.
  iIntros "* H". iNamed "H". iNamed "Hown_err".

  do 2 wp_loadField.
  wp_apply (wp_checkServErr with "[//]").
  iIntros (->). iNamed "Herr".
  do 3 wp_storeField.
  iApply "HΦ".
  iFrame "#".
  iFrame "Hptr_epoch Hptr_isReg Hptr_alicePk".
  iFrame "Hsl_pk".
  iFrame "Hreg".
  simpl in *.
  iClear "Hptr_serv_good Hptr_cli Hptr_evid Hptr_err Hevid".
  iClear "%".
  simpl in *.

  eassert (Frame false
                                  (Client.own ptr_cli
                                     (set Client.next_epoch
                                        (λ _ : w64,
                                           w64_word_instance.(word.add) ep
                                             (W64 1))
                                        {|
                                          Client.γ := cli_γ;
                                          Client.uid := W64 1;
                                          Client.next_ver := next_ver;
                                          Client.next_epoch := W64 0;
                                          Client.serv := serv;
                                          Client.serv_is_good := serv_good
                                        |}))
                                  ("Hown_cli"
                                   ∷ Client.own ptr_cli
                                       {|
                                         Client.γ := cli_γ;
                                         Client.uid := W64 1;
                                         Client.next_ver :=
                                           ?[next_ver];
                                         Client.next_epoch :=
                                           w64_word_instance.(word.add) ep
                                             (W64 1);
                                         Client.serv := serv;
                                         Client.serv_is_good := serv_good
                                       |}) ?[Q]).
  { Set Typeclasses Debug.
    Set Debug "tactic-unification".
    (* TODO: leftoff here. some hacks:
    1) remember (word.add ep (W64 1)) as hello
    2) rewrite /named
    3) unfold set
    *)
    Fail Timeout 5 eapply class_instances_frame.frame_here.
Admitted.

Lemma wp_testAll ptr_setup setup :
  {{{
    "#Hsetup" ∷ setupParams.valid ptr_setup setup false true
  }}}
  testAll #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testAll. iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hsetup".
  iClear "His_good_serv". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk").
  iIntros (ptr_cli_al) "*". iNamedSuffix 1 "_al".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_al) "Hptr_al". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk").
  iIntros (ptr_cli_bob) "*". iNamedSuffix 1 "_bob".
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_bob) "Hptr_bob".

  wp_apply (wp_NewWaitGroup nroot (λ wg_id,
    match uint.Z wg_id with
    | 0%Z => ∃ next_ep hist, own_alice ptr_al cli_γ next_ep hist
    | 1%Z => ∃ next_ep ep is_reg pk, bob_post ptr_bob cli_γ0 next_ep ep is_reg pk
    | _ => True
    end)%I).
  iIntros "* Hown_wg".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|]. iIntros "[Hown_wg Hown_tok0]".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|]. iIntros "[Hown_wg Hown_tok1]".
  replace (word.add (word.add (W64 0) (W64 1)) (W64 1)) with (W64 2); [|word].
  iDestruct (own_WaitGroup_to_is_WaitGroup with "[$Hown_wg]") as "#His_wg".

  iDestruct (struct_fields_split with "Hptr_al") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "cli") as "#Hptr_cli_al".
  wp_apply (wp_fork with "[Hown_cli_al hist Hown_tok0]").
  { iIntros "!>".
    wp_apply (wp_alice__run [] with "[$Hown_cli_al $Hptr_cli_al hist]").
    { iExists Slice.nil. iSplitL; [iFrame|iApply mk_hist]. }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok0 $Hown_al //]"). }

  iDestruct (struct_fields_split with "Hptr_bob") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "cli") as "#Hptr_cli_bob".
  wp_apply (wp_fork with "[Hown_cli_bob epoch isReg alicePk Hown_tok1]").
  { iIntros "!>".
    wp_apply (wp_bob__run with "[$Hown_cli_bob $Hptr_cli_bob $epoch $isReg alicePk]").
    { iExists Slice.nil. iFrame.
      iExists (DfracOwn 1). iApply own_slice_to_small. iApply own_slice_zero. }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok1 $Hbob_post //]"). }

  wp_apply (wp_WaitGroup__Wait with "[$Hown_wg]"). iIntros "H".
  iDestruct (big_sepS_delete _ _ (W64 0) with "H") as "[H0 H]"; [set_solver|].
  iDestruct (big_sepS_delete _ _ (W64 1) with "H") as "[H1 _]"; [set_solver|].
  iDestruct "H0" as "[%|H0]". { exfalso. word. }
  iDestruct "H1" as "[%|H1]". { exfalso. word. }
  iSimpl in "H0 H1".
  iRename "Hptr_cli_al" into "Hptr0". iRename "Hptr_cli_bob" into "Hptr1".
  iDestruct "H0" as (?) "H0". iNamedSuffix "H0" "_al".
  iDestruct "H1" as (?) "H1". iNamed "H1". iNamedSuffix "Hown_bob" "_bob".
  iDestruct (struct_field_pointsto_agree with "Hptr0 Hptr_cli_al") as %->.
  iDestruct (struct_field_pointsto_agree with "Hptr1 Hptr_cli_bob") as %->.
  iClear "His_wg Hptr0 Hptr1".

  wp_loadField. wp_apply (wp_Client__SelfMon with "Hown_cli_al").
  iIntros (selfMonEp ? err) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al".
  destruct err.(clientErr.err). { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al".
  wp_loadField. wp_apply wp_Assume. iIntros "%". case_bool_decide; [|done].
  do 2 wp_loadField. wp_apply (wp_updAdtrsAll with "Hsl_adtrAddrs").
  do 3 wp_loadField.
  iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %Hlen0.
  wp_apply (wp_doAudits with "[$Hown_cli_al $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  iNamedSuffix 1 "_al". do 3 wp_loadField.
  wp_apply (wp_doAudits with "[$Hown_cli_bob $Hsl_adtrAddrs $Hsl_adtrPks $Hdim0_adtrPks]").
  { iPureIntro. lia. }
  iNamedSuffix 1 "_bob". do 2 wp_loadField.
  simpl in *.
  iClear "Hptr_servAddr Hptr_servSigPk Hsl_servSigPk Hptr_servVrfPk Hptr_adtrAddrs
    Hsl_adtrAddrs Hptr_adtrPks Hsl_adtrPks Hdim0_adtrPks Hptr_cli_al Hptr_cli_bob
    Hptr_hist_al Hptr_epoch_bob Hown_cli_al Hown_cli_bob".

  (* the important part. *)
  wp_apply (wp_GetHist with "Hown_hist_al"). iIntros "*". iNamed 1. wp_loadField.
  iDestruct "His_good_adtrs" as (??) "[%Hlook_pk His_pk]".
  iDestruct (big_sepL_lookup with "Haudits_al") as "Haudit_al"; [exact Hlook_pk|].
  iDestruct (big_sepL_lookup with "Haudits_bob") as "Haudit_bob"; [exact Hlook_pk|].
  iDestruct ("Haudit_al" with "His_pk") as "H". iNamedSuffix "H" "_al".
  iDestruct ("Haudit_bob" with "His_pk") as "H". iNamedSuffix "H" "_bob".
  iNamed "Hown_hist". iClear "Hsl_hist".
  iDestruct (hist_extend_selfmon with "[$His_hist $His_bound_al]") as "His_hist_new"; [word..|].
  iDestruct (hist_audit_msv ep with "[$His_hist_new $His_audit_al]") as "#Hmsv_al"; [word..|].
  iDestruct (get_audit_msv with "[$His_other_key $His_audit_bob]") as "#Hmsv_bob"; [word|].
  iDestruct (msv_agree with "[]") as %?.
  { iSplit; [iFrame "Hmsv_al"|iFrame "Hmsv_bob"]. }
  iClear "His_pk His_bound_al His_audit_al His_audit_bob Hdim0_hist His_hist
    His_hist_new Hmsv_al Hmsv_bob Hptr_isReg_bob His_other_key".

  destruct (get_lat hist ep) as [[??]|], is_reg; [|done..|].
  - destruct Heq_lat. simplify_eq/=. wp_apply wp_Assert; [done|]. wp_loadField.
    wp_apply (wp_BytesEqual sl_pk sl_alicePk with "[$Hsl_pk $Hsl_alicePk_bob]").
    iIntros "_". wp_apply wp_Assert; [by case_bool_decide|].
    wp_pures. by iApply "HΦ".
  - simplify_eq/=. wp_apply wp_Assert; [done|]. wp_pures. by iApply "HΦ".
Qed.

End proof.
