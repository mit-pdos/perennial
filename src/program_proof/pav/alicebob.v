From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import alicebob.

From Perennial.program_proof.pav Require Import
  advrpc alicebob_helpers auditor core client client_hist cryptoffi
  get_agreement logical_audit logical_hist msv phys_hist rpc serde server.
From Perennial.program_proof Require Import std_proof.
From Perennial.goose_lang.lib Require Import waitgroup.

Notation alice_uid := (W64 0) (only parsing).
Notation bob_uid := (W64 1) (only parsing).

Module setupParams.
Record t :=
  mk {
    serv_good: bool;
    servAddr: w64;
    serv: Server.t;
    adtr_good: bool;
    adtrAddrs: list w64;
    adtr_pks: list (list w8);
  }.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ sl_servSigPk sl_serv_vrf_pk sl_adtrAddrs sl_adtrPks dim0_adtrPks,
  "Hptr_serv_good" ∷ ptr ↦[setupParams :: "servGood"] #obj.(serv_good) ∗
  "#Hptr_servAddr" ∷ ptr ↦[setupParams :: "servAddr"]□ #obj.(servAddr) ∗
  "#Hptr_servSigPk" ∷ ptr ↦[setupParams :: "servSigPk"]□ (slice_val sl_servSigPk) ∗
  "#Hptr_serv_vrf_pk" ∷ ptr ↦[setupParams :: "servVrfPk"]□ (slice_val sl_serv_vrf_pk) ∗
  "Hptr_adtr_good" ∷ ptr ↦[setupParams :: "adtrGood"] #obj.(adtr_good) ∗
  "#Hptr_adtrAddrs" ∷ ptr ↦[setupParams :: "adtrAddrs"]□ (slice_val sl_adtrAddrs) ∗
  "#Hptr_adtrPks" ∷ ptr ↦[setupParams :: "adtrPks"]□ (slice_val sl_adtrPks) ∗

  "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded obj.(serv).(Server.sig_pk) ∗
  "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded obj.(adtrAddrs) ∗
  "#Hsl_adtrPks" ∷ own_slice_small sl_adtrPks (slice.T byteT) DfracDiscarded dim0_adtrPks ∗
  "#Hsl_serv_vrf_pk" ∷ own_slice_small sl_serv_vrf_pk byteT DfracDiscarded obj.(serv).(Server.vrf_pk) ∗

  "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;obj.(adtr_pks),
    own_slice_small p byteT DfracDiscarded o) ∗

  "#His_good_serv" ∷ (if negb obj.(serv_good) then True else
    is_sig_pk obj.(serv).(Server.sig_pk) (sigpred obj.(serv).(Server.γhist))) ∗
  "#His_good_adtrs" ∷ (if negb obj.(adtr_good) then True else
    ∃ i sig_pk γadtr,
    "%Hlook_adtr" ∷ ⌜ obj.(adtr_pks) !! i = Some sig_pk ⌝ ∗
    "#His_good_adtr" ∷ is_sig_pk sig_pk (sigpred γadtr)) ∗
  "%Hlen_addr_pk" ∷ ⌜ length obj.(adtrAddrs) = length obj.(adtr_pks) ⌝.

End defs.
End setupParams.

Section proof.
Context `{!heapGS Σ, !pavG Σ, !waitgroupG Σ}.

Lemma wp_setup (uids : gset w64) (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  setup #servAddr (slice_val sl_adtrAddrs)
  {{{
    ptr_setup serv adtr_pks, RET #ptr_setup;
    "Hsetup" ∷ setupParams.own ptr_setup (setupParams.mk true
      servAddr serv true adtrAddrs adtr_pks) ∗
    "Huids" ∷ [∗ set] u ∈ uids, u ↪[serv.(Server.γvers)] W64 0
  }}}.
Proof.
  rewrite /setup. iIntros (Φ) "H HΦ". iNamed "H".
  wp_apply (wp_NewServer uids).
  iIntros "*". iNamed 1.
  iPoseProof "Hserv" as "H". iNamed "H".
  wp_apply (wp_VrfPublicKeyEncode with "Hptr_vrf_pk").
  iIntros "*". iNamedSuffix 1 "_vrf".
  iPersist "Hsl_enc_vrf".
  wp_apply (wp_NewRpcServer with "Hserv"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_ref_of_zero; [done|]. iIntros (?) "Hptr_adtrPks".
  wp_apply (wp_forSlicePrefix
    (λ doneV _, ∃ sl_adtrPks dim0_adtrPks adtrPks,
    "Hptr_adtrPks" ∷ l ↦[slice.T (slice.T byteT)] (slice_val sl_adtrPks) ∗
    "Hsl_adtrPks" ∷ own_slice sl_adtrPks (slice.T byteT) (DfracOwn 1) dim0_adtrPks ∗
    "#Hdim0_adtrPks" ∷ ([∗ list] p;o ∈ dim0_adtrPks;adtrPks,
      own_slice_small p byteT DfracDiscarded o) ∗
    "#His_adtrPks" ∷ ([∗ list] x ∈ adtrPks,
      ∃ γadtr, is_sig_pk x (sigpred γadtr)) ∗
    "%Hlen_adtrPks" ∷ ⌜ length doneV = length dim0_adtrPks ⌝)%I
    with "[] [$Hsl_adtrAddrs Hptr_adtrPks]").
  { clear. iIntros "* _". iIntros (Φ) "!>". iIntros "(%&%&%&H) HΦ". iNamed "H".
    wp_apply wp_NewAuditor. iIntros "*". iNamed 1.
    wp_apply (wp_NewRpcAuditor with "Hvalid_adtr"). iIntros "*". iNamed 1.
    wp_apply (wp_Server__Serve with "Hown_rpcserv").
    wp_load. wp_apply (wp_SliceAppend with "Hsl_adtrPks"). iIntros "* Hsl_adtrPks".
    wp_store. iApply "HΦ". iFrame.
    iExists (adtrPks ++ [adtrPk]). iIntros "!>". iSplit; [|iSplit].
    - iApply big_sepL2_snoc. iFrame "#".
    - by iFrame "#".
    - iPureIntro. rewrite !length_app. solve_length. }
  { iExists Slice.nil, [], []. iFrame. iSplit; [|naive_solver].
    iApply own_slice_zero. }
  iIntros "[_ (%&%&%&H)]". iNamed "H".
  wp_apply wp_Sleep. wp_load. iApply wp_fupd.

  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iPersist "servAddr servSigPk servVrfPk adtrAddrs adtrPks".
  iDestruct (own_slice_to_small with "Hsl_adtrPks") as "Hsl_adtrPks".
  iMod (own_slice_small_persist with "Hsl_adtrPks") as "#Hsl_adtrPks".

  iIntros "!>". iApply "HΦ".
  iFrame "∗#". simpl.
  do 2 try iSplit.
  - iDestruct (is_sig_sk_to_pk with "HsigSk") as "$".
  - iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %Hlen.
    list_elem adtrPks 0 as adtrPk.
    iDestruct (big_sepL_lookup with "His_adtrPks") as "[% His_adtrPk]"; [exact HadtrPk_lookup|].
    iFrame "#%".
  - iDestruct (big_sepL2_length with "Hdim0_adtrPks") as %?. iPureIntro. lia.
Qed.

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
  there are many other possible hacks. see git log for more details. *)
  rewrite /named.
  by iFrame.
Qed.

Lemma wp_testAliceBob setup ptr_setup :
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

  (* the final part. *)
  wp_loadField.
  wp_apply wp_Assume.
  iIntros (Hlt_ep).
  apply bool_decide_eq_true in Hlt_ep.
  do 2 wp_loadField.
  list_elem selfmon_hist (uint.nat ep) as alice_orig_pk.
  { subst selfmon_hist. rewrite length_app length_replicate. word. }
  wp_apply (wp_hist_SliceGet with "[$Hown_hist_al]"); [done|].
  iIntros "*". iNamed 1.

  iAssert (
    |==>
    "Hcli_al" ∷ ClientHist.own ptr_cli (ClientHist.mk _ _ _ _
      setup.(setupParams.serv_good)) ∗
    "Hcli_bob" ∷ Client.own ptr_cli0 (Client.mk _ _ _ _ _
      setup.(setupParams.serv_good)) ∗

    "#Haudit_serv" ∷ (if negb setup.(setupParams.serv_good) then True else
      "#Haudit_al" ∷ logical_audit γ _ _ _ ∗
      "#Haudit_bob" ∷ logical_audit γ0 _ _ _)
    )%I with "[Hcli_al Hcli_bob]" as "H".
  { destruct setup.(setupParams.serv_good) eqn:Heq_good; [|by iFrame].
    rewrite /ClientHist.own /=.
    iNamedSuffix "Hcli_al" "_al".
    iMod (good_serv_logical_audit (Client.mk _ _ _ _ _ true)) as "H"; [done|].
    iDestruct ("H" with "Hcli_al") as "#Haudit_al /=".
    iMod (good_serv_logical_audit (Client.mk _ _ _ _ _ true)) as "H"; [done|].
    iDestruct ("H" with "Hcli_bob") as "#Haudit_bob /=".
    iEval (replace next_epoch with (W64 $ length selfmon_hist) by word)
      in "Haudit_al Haudit_bob".
    by iFrame "∗#". }
  iMod "H". iNamed "H".

  iAssert (
    ∃ γadtr,
    "#Haudit_al" ∷ logical_audit γ γadtr _ _ ∗
    "#Haudit_bob" ∷ logical_audit γ0 γadtr _ _
  )%I as "#H".
  { destruct Hgood as [-> | ->]; iFrame "#". }
  iNamed "H". iClear "Haudit_auditor Haudit_serv".

  iAssert (⌜ alice_orig_pk = if is_reg then Some alice_pk else None ⌝)%I as %->.
  { iDestruct (ClientHist.lookup_msv with "Hcli_al Haudit_al") as "#Hmsv_al /="; [done|..].
    { subst selfmon_hist. rewrite length_app length_replicate. word. }
    destruct is_reg; simpl; iNamed "Hbob_post".
    + iDestruct (get_Some_to_msv with "His_get_post Haudit_bob") as "#Hmsv_bob"; [word|].
      by iDestruct (msv_agree with "Hmsv_al Hmsv_bob") as %->.
    + iDestruct (get_None_to_msv with "His_get_post Haudit_bob") as "#Hmsv_bob"; [word|].
      by iDestruct (msv_agree with "Hmsv_al Hmsv_bob") as %->. }

  destruct is_reg; simpl; iNamed "Hbob_post"; iNamed "Hhist_entry".
  - do 2 wp_loadField.
    wp_apply wp_Assert; [done|].
    do 3 wp_loadField.
    wp_apply (wp_BytesEqual with "[Hsl_alicePk_bob]"); [by iFrame "∗#"|].
    iIntros "_".
    wp_apply wp_Assert; [by case_bool_decide|].
    wp_pures. by iApply "HΦ".
  - do 2 wp_loadField.
    wp_apply wp_Assert; [done|].
    wp_loadField.
    wp_pures. by iApply "HΦ".
Qed.

Lemma wp_testSecurity (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  testSecurity #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof using Type*.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H".
  wp_apply (wp_setup {[ alice_uid; bob_uid ]}); [iFrame "#%"|].
  iIntros "*". iNamed 1.
  iClear "Hsl_adtrAddrs". iNamed "Hsetup". simpl in *.
  do 2 wp_storeField.
  wp_apply (wp_testAliceBob (setupParams.mk _ _ _ _ _ _)
    with "[Hptr_serv_good Hptr_adtr_good Huids]").
  { iDestruct (big_sepS_insert with "Huids") as "[Huid_al Huid_bob]"; [set_solver|].
    rewrite big_sepS_singleton.
    iFrame "∗#%". naive_solver. }
  wp_pures. by iApply "HΦ".
Qed.

Lemma wp_testCorrectness (servAddr : w64) sl_adtrAddrs (adtrAddrs : list w64) :
  {{{
    "#Hsl_adtrAddrs" ∷ own_slice_small sl_adtrAddrs uint64T DfracDiscarded adtrAddrs ∗
    "%Hlen_adtrs" ∷ ⌜ length adtrAddrs > 0 ⌝
  }}}
  testCorrectness #servAddr (slice_val sl_adtrAddrs)
  {{{ RET #(); True }}}.
Proof using Type*.
  iIntros (Φ) "H HΦ". wp_rec. iNamed "H".
  wp_apply (wp_setup {[ alice_uid; bob_uid ]}); [iFrame "#%"|].
  iIntros "*". iNamed 1.
  iClear "Hsl_adtrAddrs". iNamed "Hsetup". simpl in *.
  do 2 wp_storeField.
  wp_apply (wp_testAliceBob (setupParams.mk _ _ _ _ _ _)
    with "[Hptr_serv_good Hptr_adtr_good Huids]").
  { iDestruct (big_sepS_insert with "Huids") as "[Huid_al Huid_bob]"; [set_solver|].
    rewrite big_sepS_singleton.
    iFrame "∗#%". naive_solver. }
  wp_pures. by iApply "HΦ".
Qed.

(*
Print Assumptions wp_testSecurity.
Print Assumptions wp_testCorrectness.

# Axioms

## misc
wp_updAdtrsAll

## server
wp_NewServer
wp_CallServSelfMon
wp_CallServPut
wp_CallServGet
Server.own

## auditor
wp_NewAuditor
wp_CallAdtrGet

## serde
PreSigDig.wp_enc
MapValPre.wp_enc
MapLabelPre.wp_enc
CommitOpen.wp_enc
merkle.MerkleProof.wp_dec

## rpc
wp_Server__Serve
wp_NewRpcServer
wp_NewRpcAuditor

## rpc ffi (trusted)
wp_Dial
advrpc.Server.t
own_Client

## crypto ffi (trusted)
wp_VrfPublicKey__Verify
wp_VrfPublicKeyEncode
wp_VrfPublicKeyDecode
wp_SigPublicKey__Verify
wp_NewHasher
own_hasher
is_vrf_sk_persistent
is_vrf_sk
is_vrf_proof_persistent
is_vrf_proof
is_vrf_pk_persistent
is_vrf_pk
is_vrf_out_persistent
is_vrf_out_det
is_vrf_out
is_sig_to_pred
is_sig_sk_to_pk
is_sig_sk_persistent
is_sig_sk
is_sig_pk_persistent
is_sig_pk
is_sig_persistent
is_sig
is_hash_persistent
is_hash_len
is_hash_inj
is_hash_det
is_hash
wp_Hasher__Write
wp_Hasher__Sum
*)

End proof.
