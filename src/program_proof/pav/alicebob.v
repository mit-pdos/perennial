From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import alicebob.

From Perennial.program_proof.pav Require Import
  advrpc alicebob_helpers core client client_hist cryptoffi
  get_agreement logical_hist msv phys_hist rpc serde server.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import waitgroup.

Notation alice_uid := (W64 0) (only parsing).
Notation bob_uid := (W64 1) (only parsing).

Section proof.
Context `{!heapGS Σ, !pavG Σ, !waitGroupG Σ}.

Definition own_alice ptr cli_γ serv (serv_good : bool) : iProp Σ :=
  ∃ (ptr_cli : loc) sl_hist epochs,
  "#Hptr_serv_good" ∷ ptr ↦[alice :: "servGood"]□ #serv_good ∗
  "#Hptr_cli" ∷ ptr ↦[alice :: "cli"]□ #ptr_cli ∗
  "Hptr_hist" ∷ ptr ↦[alice :: "hist"] (slice_val sl_hist) ∗

  "Hown_cli" ∷ ClientHist.own ptr_cli (ClientHist.mk cli_γ alice_uid
    epochs serv serv_good) ∗
  "Hown_hist" ∷ own_hist sl_hist epochs.

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

Global Instance bob_post_pers a0 a1 is_reg a3 a4 : Persistent (bob_post a0 a1 is_reg a3 a4).
Proof. destruct is_reg; apply _. Qed.

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
  iIntros (->). iNamed "Herr".
  wp_loadField.
  wp_apply (wp_extendHist with "[$Hown_hist]"); [word|].
  iIntros "*". iNamed 1.
  wp_storeField.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros "* H".
  iPersist "H".
  iDestruct (struct_fields_split with "H") as "{H} H". iNamed "H".
  wp_loadField.
  iNamed "Hown_hist".
  wp_apply (wp_SliceAppend with "Hsl_hist").
  iIntros "* Hsl_hist".
  wp_storeField.

  iApply "HΦ". iFrame "∗#". simpl.
  rewrite (assoc (++)).
  iPersist "Hsl_pk".
  iFrame "#". naive_solver.
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
  (* TODO: bug causing unification to fail, unless we do a hack like this.
  see git log for more details. *)
  rewrite /named.
  by iFrame.
Qed.

Lemma wp_testAliceBob ptr_setup setup :
  {{{
    "Hsetup" ∷ setupParams.own ptr_setup setup ∗
    "Huid_al" ∷ alice_uid ↪[setup.(setupParams.serv).(Server.γvers)] W64 0 ∗
    "Huid_bob" ∷ bob_uid ↪[setup.(setupParams.serv).(Server.γvers)] W64 0 ∗
    "%Hgood" ∷ ⌜ setup.(setupParams.serv_good) = true ∨ setup.(setupParams.adtr_good) = true ⌝
  }}}
  testAliceBob #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H". iNamed "Hsetup".
  do 3 wp_loadField.
  wp_apply (wp_NewClient with "[Huid_al]").
  { iFrame "#". case_match; [done|by iFrame]. }
  iIntros (ptr_cli_al) "*". iNamedSuffix 1 "_al".
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_al) "Hptr_al". do 3 wp_loadField.
  wp_apply (wp_NewClient with "[Huid_bob]").
  { iFrame "#". case_match; [done|by iFrame]. }
  iIntros (ptr_cli_bob) "*". iNamedSuffix 1 "_bob".
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|].
  iIntros (ptr_bob) "Hptr_bob".

  wp_apply (wp_NewWaitGroup (Σ:=Σ) nroot (λ wg_id,
    match uint.Z wg_id with
    | 0%Z =>
      "Hown_al" ∷ own_alice _ _ _ _
    | 1%Z =>
      ∃ is_reg ep alice_pk,
      "Hown_bob" ∷ own_bob _ _ _ _ true is_reg ep alice_pk ∗
      "#Hbob_post" ∷ bob_post _ _ is_reg ep alice_pk
    | _ => True%I
    end)%I).
  iIntros "* Hown_wg".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|].
  iIntros "[Hown_wg Hown_tok0]".
  wp_apply (wp_WaitGroup__Add with "[$Hown_wg]"); [word|].
  iIntros "[Hown_wg Hown_tok1]".
  replace (word.add (word.add _ _) _) with (W64 2) by word.
  replace (word.add _ _) with (W64 1) by word.
  iDestruct (own_WaitGroup_to_is_WaitGroup with "[$Hown_wg]") as "#His_wg".

  iDestruct (struct_fields_split with "Hptr_al") as "H". iNamed "H".
  iPersist "servGood cli".
  wp_apply (wp_fork with "[Hown_cli_al hist Hown_tok0]").
  { iIntros "!>".
    wp_apply (wp_alice__run with "[Hown_cli_al hist]").
    { iFrame "#". iExists Slice.nil, []. iFrame "hist".
      iDestruct phys_hist.mk_hist as "$".
      iExists []. simpl. iFrame.
      by iDestruct logical_hist.mk_hist as "$". }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok0 $Hown_al //]"). }
  iClear "servGood cli".

  iDestruct (struct_fields_split with "Hptr_bob") as "H". iNamed "H".
  iPersist "servGood cli".
  wp_apply (wp_fork with "[Hown_cli_bob epoch isReg alicePk Hown_tok1]").
  { iIntros "!>".
    wp_apply (wp_bob__run with "[$Hown_cli_bob $epoch $isReg alicePk]").
    { iExists Slice.nil. iFrame "∗#".
      by iDestruct own_slice_small_nil as "$". }
    iIntros "*". iNamed 1.
    by wp_apply (wp_WaitGroup__Done with "[$His_wg $Hown_tok1 $Hown_bob $Hbob_post //]"). }
  iClear "servGood cli".

  wp_apply (wp_WaitGroup__Wait with "[$Hown_wg]"). iIntros "H".
  iDestruct (big_sepS_delete _ _ (W64 0) with "H") as "[H0 H]"; [set_solver|].
  iDestruct (big_sepS_delete _ _ (W64 1) with "H") as "[H1 _]"; [set_solver|].
  iDestruct "H0" as "[%|H0]"; [word|].
  iDestruct "H1" as "[%|H1]"; [word|].
  iSimpl in "H0 H1".
  iNamed "H0". iNamed "H1".
  iNamedSuffix "Hown_al" "_al". iNamedSuffix "Hown_bob" "_bob".
  iClear "His_wg".

  wp_loadField.
  wp_apply (wp_ClientHist__SelfMon with "Hown_cli_al").
  iIntros "*". iNamedSuffix 1 "_al". simpl.
  iNamedSuffix "Hown_err_al" "_al".
  do 2 wp_loadField.
  wp_apply (wp_checkServErr with "[//]").
  iIntros (->).
  iNamedSuffix "Herr_al" "_al".
  iClear (Hgenie_al) "Hptr_evid_al Hptr_err_al Hevid_al".
  wp_loadField.
  wp_apply (wp_extendHist with "[$Hown_hist_al]"); [word|].
  iIntros "*". iNamedSuffix 1 "_al".
  wp_storeField.
  replace (uint.Z (word.add _ _) - length epochs)%Z with
    (uint.Z ep0 + 1 - length epochs)%Z by word.
  iEval (rewrite /set /=) in "Hcli_al".
  remember (epochs ++ _) as selfmon_hist.

  wp_loadField.
  Typeclasses Opaque Client.own logical_audit.
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ _,
    "Hcli_al" ∷ ClientHist.own ptr_cli _ ∗
    "Hcli_bob" ∷ Client.own ptr_cli0 _ ∗

    "#Haudit_auditor" ∷ (if negb setup.(setupParams.adtr_good) then True else
      ∃ γadtr,
      "#Haudit_al" ∷ logical_audit γ γadtr _ _ ∗
      "#Haudit_bob" ∷ logical_audit γ0 γadtr _ _)
    )%I
    with "[Hcli_al Hown_cli_bob]"
  ).
  { wp_if_destruct; [|by iFrame].
    do 2 wp_loadField.
    wp_apply (wp_updAdtrsAll with "Hsl_adtrAddrs").
    do 3 wp_loadField.
    iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %?.
    rewrite /ClientHist.own /=.
    iNamedSuffix "Hcli_al" "_al".
    wp_apply (wp_doAudits with "[$Hcli_al]").
    { iFrame "#". iPureIntro. lia. }
    simpl. iNamedSuffix 1 "_al".
    do 3 wp_loadField.
    wp_apply wp_ncfupd.
    wp_apply (wp_doAudits with "[$Hown_cli_bob]").
    { iFrame "#". iPureIntro. lia. }
    simpl. iNamedSuffix 1 "_bob".

    iNamed "His_good_adtrs".
    iDestruct (big_sepL_lookup with "Haudits_al") as "H"; [done|].
    iMod ("H" $! γadtr with "His_good_adtr") as "H".
    iNamedSuffix "H" "_al".
    iDestruct (big_sepL_lookup with "Haudits_bob") as "H"; [done|].
    iMod ("H" $! γadtr with "His_good_adtr") as "H".
    iNamedSuffix "H" "_bob".
    iEval (replace next_epoch with (W64 $ length selfmon_hist) by word) in "His_audit_al".
    by iFrame "∗#". }
  iIntros "*". iNamed 1.
  iClear "Hptr_servAddr Hptr_servSigPk Hsl_servSigPk Hptr_serv_vrf_pk Hptr_adtrAddrs
    Hsl_adtrAddrs Hptr_adtrPks Hsl_adtrPks Hdim0_adtrPks Hptr_cli_al Hptr_cli_bob".

  (* the important part. *)
  wp_loadField.
  wp_apply wp_Assume.
  iIntros (Hlt_ep).
  apply bool_decide_eq_true in Hlt_ep.
  do 2 wp_loadField.
  list_elem selfmon_hist (uint.nat ep) as alice_orig_pk.
  { subst selfmon_hist. rewrite length_app length_replicate. word. }
  wp_apply (wp_hist_SliceGet with "[$Hown_hist_al]"); [done|].
  iIntros "*". iNamed 1. iNamed "Hhist_entry".

  iAssert (
    |==>
    "Hcli_al" ∷ ClientHist.own ptr_cli _ ∗
    "Hcli_bob" ∷ Client.own ptr_cli0 _ ∗

    "#Haudit_serv" ∷ (if negb setup.(setupParams.serv_good) then True else
      "#Haudit_al" ∷ logical_audit γ _ _ _ ∗
      "#Haudit_bob" ∷ logical_audit γ0 _ _ _)
    )%I with "[Hcli_al Hcli_bob]" as "H".
  { destruct setup.(setupParams.serv_good) eqn:Heq_good; [|by iFrame].
    rewrite /ClientHist.own /=.
    iNamedSuffix "Hcli_al" "_al".
    (* TODO: good_serv_logical_audit consumes Client.own,
    even tho it doesn't need to.
    need to strengthen that lemma to bring bupd forward. *)
    iMod (good_serv_logical_audit with "Hcli_al") as "#H /="; [done|].
    iEval (replace next_epoch with (W64 $ length selfmon_hist) by word) in "H".
    iFrame "H". iClear "H".
    admit. }
Admitted.

End proof.
