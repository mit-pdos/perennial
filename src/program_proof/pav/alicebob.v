From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc auditor core client cryptoffi rpc serde server test_helpers.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import waitgroup.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own_alice ptr cli_γ next_ep hist : iProp Σ :=
  ∃ ptr_cli a1 a2 a3 a4 sl_hist,
  "Hown_cli" ∷ client.Client.own ptr_cli
    (client.Client.mk cli_γ (W64 0) (W64 $ length hist) next_ep a1 a2 a3 a4) ∗
  "#Hptr_cli" ∷ ptr ↦[alice :: "cli"]□ #ptr_cli ∗
  "Hptr_hist" ∷ ptr ↦[alice :: "hist"] (slice_val sl_hist) ∗
  "Hown_hist" ∷ own_hist cli_γ (W64 0) sl_hist hist next_ep.

Definition own_bob ptr cli_γ next_ep (ep : w64) (is_reg : bool) (pk : list w8) : iProp Σ :=
  ∃ ptr_cli a1 a2 a3 a4 a5 sl_alicePk d0,
  "Hown_cli" ∷ client.Client.own ptr_cli
    (client.Client.mk cli_γ (W64 1) a1 next_ep a2 a3 a4 a5) ∗
  "#Hptr_cli" ∷ ptr ↦[bob :: "cli"]□ #ptr_cli ∗
  "Hptr_epoch" ∷ ptr ↦[bob :: "epoch"] #ep ∗
  "Hptr_isReg" ∷ ptr ↦[bob :: "isReg"] #is_reg ∗
  "Hptr_alicePk" ∷ ptr ↦[bob :: "alicePk"] (slice_val sl_alicePk) ∗
  "Hsl_alicePk" ∷ own_slice_small sl_alicePk byteT d0 pk.

Definition bob_post ptr cli_γ next_ep ep is_reg pk : iProp Σ :=
  ∃ ep',
  "Hown_bob" ∷ own_bob ptr cli_γ next_ep ep is_reg pk ∗
  "His_other_key" ∷ is_other_key cli_γ (W64 0) ep
    (if is_reg then Some (ep', pk) else None) ∗
  "%Heq_ep" ∷ ⌜ (uint.Z ep + 1)%Z = uint.Z next_ep ⌝.

End defs.

Section wps.
Context `{!heapGS Σ, !pavG Σ, !waitgroupG Σ}.

Lemma wp_alice__run hist ptr cli_γ next_ep :
  {{{
    "Hown_al" ∷ own_alice ptr cli_γ next_ep hist
  }}}
  alice__run #ptr
  {{{
    next_ep' hist', RET #();
    "Hown_al" ∷ own_alice ptr cli_γ next_ep' hist'
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". rewrite /alice__run.
  wp_apply wp_ref_to; [val_ty|]. iIntros "* Hptr_i".
  wp_apply (wp_forUpto
    (λ _, ∃ next_ep' hist', own_alice ptr cli_γ next_ep' hist')%I
    with "[] [$Hown_al $Hptr_i]"); [word|..].
  { clear. iIntros (? Φ) "!> H HΦ". iDestruct "H" as "((%&%&Hown_al)&Hptr_i&%)".
    wp_apply wp_Sleep. wp_apply wp_SliceSingleton; [val_ty|]. iIntros (?) "Hsl_pk".
    iNamed "Hown_al". wp_loadField.
    wp_apply (wp_Client__Put with "[$Hown_cli Hsl_pk]").
    { iApply own_slice_to_small. instantiate (1:=[(W8 1)]). iFrame "Hsl_pk". }
    iIntros "* H". iNamed "H". simpl in *. wp_pures. wp_loadField.
    wp_apply wp_Assume. iIntros "%Herr".
    apply negb_true_iff in Herr. rewrite Herr. iNamed "H".
    wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Hptr_e".
    wp_loadField. iNamed "Hown_hist".
    wp_apply (wp_SliceAppend with "Hsl_hist"). iIntros (?) "Hsl_hist".
    wp_storeField.

    iApply "HΦ".
    iMod (struct_pointsto_persist with "Hptr_e") as "#Hptr_e".
    iDestruct (struct_fields_split with "Hptr_e") as "H". iNamed "H".
    iMod (own_slice_small_persist with "Hsl_pk") as "#Hsl_pk".
    iDestruct (hist_extend_put with "[$His_hist $His_key]") as "His_hist_new"; [word..|].
    iFrame "Hptr_i Hptr_hist Hptr_cli Hsl_hist His_hist_new".
    rewrite length_app. simpl.
    replace (W64 (length hist' + 1)%nat) with (word.add (W64 1) (W64 $ length hist')) by word.
    iFrame "Hown_cli". iApply big_sepL2_snoc. by iFrame "#". }
  iIntros "((%&%&Hown_al)&_)". wp_pures. by iApply ("HΦ" $! next_ep' hist').
Qed.

Lemma wp_bob__run ptr cli_γ next_ep ep is_reg pk :
  {{{
    "Hown_bob" ∷ own_bob ptr cli_γ next_ep ep is_reg pk
  }}}
  bob__run #ptr
  {{{
    next_ep' ep' is_reg' pk', RET #();
    "Hbob_post" ∷ bob_post ptr cli_γ next_ep' ep' is_reg' pk'
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_bob". rewrite /bob__run.
  wp_apply wp_Sleep. wp_loadField. wp_apply (wp_Client__Get with "Hown_cli").
  iIntros "* H". iNamed "H". wp_loadField. iClear "Herr".
  wp_apply wp_Assume. iIntros "%Herr".
  apply negb_true_iff in Herr. rewrite Herr. iNamed "H". do 3 wp_storeField.
  iApply "HΦ". iFrame "∗#". word.
Qed.

Lemma wp_testAll ptr_setup setup :
  {{{
    "#Hsetup" ∷ setupParams.valid ptr_setup setup false true
  }}}
  testAll #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testAll. iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hsetup".
  iClear "His_good_serv". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (ptr_cli_al) "*". iNamedSuffix 1 "_al".
  wp_apply wp_allocStruct; [val_ty|]. iIntros (ptr_al) "Hptr_al". do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (ptr_cli_bob) "*". iNamedSuffix 1 "_bob".
  wp_apply wp_allocStruct; [val_ty|]. iIntros (ptr_bob) "Hptr_bob".

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

End wps.
