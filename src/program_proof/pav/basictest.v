From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import advrpc auditor core client cryptoffi rpc server.
From Perennial.program_proof Require Import std_proof.

Module setupParams.
Record t :=
  mk {
    servAddr: w64;
    servSigPk: list w8;
    serv_γ: gname;
    servVrfPk: loc;
    adtr0Addr: w64;
    adtr0Pk: list w8;
    adtr0_γ: gname;
    adtr1Addr: w64;
    adtr1Pk: list w8;
    adtr1_γ: gname;
  }.
Section defs.
Context `{!heapGS Σ, !pavG Σ}.
Definition own (ptr : loc) (obj : t) (serv_good adtrs_good : bool) : iProp Σ :=
  ∃ sl_servSigPk sl_adtr0Pk sl_adtr1Pk,
  "Hptr_servAddr" ∷ ptr ↦[setupParams :: "servAddr"] #obj.(servAddr) ∗
  "Hptr_servSigPk" ∷ ptr ↦[setupParams :: "servSigPk"] (slice_val sl_servSigPk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded obj.(servSigPk) ∗
  "#His_good_serv" ∷ (if serv_good then is_pk obj.(servSigPk) (serv_sigpred obj.(serv_γ)) else True) ∗
  "Hptr_servVrfPk" ∷ ptr ↦[setupParams :: "servVrfPk"] #obj.(servVrfPk) ∗
  "Hptr_adtr0Addr" ∷ ptr ↦[setupParams :: "adtr0Addr"] #obj.(adtr0Addr) ∗
  "Hptr_adtr0Pk" ∷ ptr ↦[setupParams :: "adtr0Pk"] (slice_val sl_adtr0Pk) ∗
  "#Hsl_adtr0Pk" ∷ own_slice_small sl_adtr0Pk byteT DfracDiscarded obj.(adtr0Pk) ∗
  "Hptr_adtr1Addr" ∷ ptr ↦[setupParams :: "adtr1Addr"] #obj.(adtr1Addr) ∗
  "Hptr_adtr1Pk" ∷ ptr ↦[setupParams :: "adtr1Pk"] (slice_val sl_adtr1Pk) ∗
  "#Hsl_adtr1Pk" ∷ own_slice_small sl_adtr1Pk byteT DfracDiscarded obj.(adtr1Pk) ∗
  "#His_good_adtrs" ∷ (if adtrs_good then
    is_pk obj.(adtr0Pk) (adtr_sigpred obj.(adtr0_γ)) ∨
    is_pk obj.(adtr1Pk) (adtr_sigpred obj.(adtr1_γ)) else True).
End defs.
End setupParams.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_setup (servAddr adtr0Addr adtr1Addr : w64) (serv_good adtrs_good : bool) :
  {{{ True }}}
  setup #servAddr #adtr0Addr #adtr1Addr
  {{{
    ptr_setup setup, RET #ptr_setup;
    "Hsetup" ∷ setupParams.own ptr_setup setup serv_good adtrs_good
  }}}.
Proof.
  rewrite /setup. iIntros (Φ) "_ HΦ".
  wp_apply wp_newServer. iIntros (???? serv_γ ?). iNamedSuffix 1 "0".
  wp_apply (wp_newRpcServer with "Hown_serv0"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply (wp_newAuditor with "Hsl_sigPk0"). iIntros (???? adtr0_γ). iNamedSuffix 1 "1".
  wp_apply (wp_newRpcAuditor with "[$Hown_adtr1]"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply (wp_newAuditor with "Hsl_sigPk0"). iIntros (???? adtr1_γ). iNamedSuffix 1 "2".
  wp_apply (wp_newRpcAuditor with "[$Hown_adtr2]"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_Sleep. wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iApply ("HΦ" $! _ (setupParams.mk _ _ serv_γ _ _ _ adtr0_γ _ _ adtr1_γ)).
  iFrame "∗#". simpl. iSplitL.
  - destruct serv_good; [iFrame "#"|done].
  - destruct adtrs_good; [iFrame "#"|done].
Qed.

Lemma wp_testBasic ptr_setup setup :
  {{{
    "Hsetup" ∷ setupParams.own ptr_setup setup false true
  }}}
  testBasic #ptr_setup
  {{{ RET #(); True }}}.
Proof using Type*.
  rewrite /testBasic. iIntros (Φ) "H HΦ". iNamed "H".
  iNamed "Hsetup". iClear "His_good_serv".

  (* alice put. *)
  do 3 wp_loadField. wp_apply (wp_newClient with "Hsl_servSigPk").
  iIntros (?????). iNamedSuffix 1 "_al".
  wp_apply wp_SliceSingleton; [val_ty|]. iIntros (?) "Hpk0".
  iDestruct (slice.own_slice_to_small with "Hpk0") as "Hpk0".
  wp_apply (wp_Client__Put with "[$Hown_cli_al Hpk0]").
  { instantiate (1:=[_]). iFrame "Hpk0". }
  iIntros (ep0 ? err0) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err0.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al".

  (* update auditors. *)
  wp_loadField. wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "0".
  wp_loadField. wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "1".
  wp_loadField. wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "2".
  wp_apply (wp_callServAudit with "Hown_cli0").
  iIntros (?? err1) "H". iNamedSuffix "H" "0". destruct err1.
  { wp_apply wp_Assume_false. }
  simpl. iNamedSuffix "H" "0". wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callServAudit with "Hown_cli0").
  iIntros (?? err2) "H". iNamedSuffix "H" "0". destruct err2.
  { wp_apply wp_Assume_false. }
  simpl. iNamedSuffix "H" "1". wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callAdtrUpdate with "[$Hown_cli1 $Hown_upd0]").
  iIntros (?) "H". iEval (rewrite /named) in "H".
  iDestruct "H" as "[Hown_cli1 Hown_upd0]".
  wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callAdtrUpdate with "[$Hown_cli1 $Hown_upd1]").
  iIntros (?) "H". iEval (rewrite /named) in "H".
  iDestruct "H" as "[Hown_cli1 Hown_upd1]".
  wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callAdtrUpdate with "[$Hown_cli2 $Hown_upd0]").
  iIntros (?) "H". iEval (rewrite /named) in "H".
  iDestruct "H" as "[Hown_cli2 Hown_upd0]".
  wp_apply wp_Assume. iIntros "_".
  wp_apply (wp_callAdtrUpdate with "[$Hown_cli2 $Hown_upd1]").
  iIntros (?) "H". iEval (rewrite /named) in "H".
  iDestruct "H" as "[Hown_cli2 Hown_upd1]".
  wp_apply wp_Assume. iIntros "_".

  (* bob get. *)
  do 3 wp_loadField.
  wp_apply (wp_newClient with "Hsl_servSigPk"). iIntros (?????). iNamedSuffix 1 "_bob".
  wp_apply (wp_Client__Get with "Hown_cli_bob").
  iIntros (is_reg ?? ep1 ? err7) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err7.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_". wp_apply wp_Assume. iIntros "%Heq_ep /=".
  iNamedSuffix "H" "_bob". iRename "H" into "Hreg".

  (* alice and bob audit. *)
  do 2 wp_loadField.
  wp_apply (wp_Client__Audit with "[$Hown_cli_al $Hsl_adtr0Pk]").
  iIntros (? err8) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err8.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al0".
  do 2 wp_loadField.
  wp_apply (wp_Client__Audit with "[$Hown_cli_al $Hsl_adtr1Pk]").
  iIntros (? err9) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err9.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al1".
  do 2 wp_loadField.
  wp_apply (wp_Client__Audit with "[$Hown_cli_bob $Hsl_adtr0Pk]").
  iIntros (? err10) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err10.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_bob0".
  do 2 wp_loadField.
  wp_apply (wp_Client__Audit with "[$Hown_cli_bob $Hsl_adtr1Pk]").
  iIntros (? err11) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err11.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_bob1".

  (* main part: proving the pk's are equal. *)
  case_bool_decide; [|done]. simplify_eq/=.
  iClear "Hsl_adtr0Pk Hsl_adtr1Pk Hown_cli0 Hown_cli1 Hown_cli2
    Hown_upd0 Hown_upd1 Hown_cli_al Hown_cli_bob
    Hptr_servAddr Hptr_servSigPk Hptr_servVrfPk Hptr_adtr0Addr Hptr_adtr0Pk
    Hptr_adtr1Addr Hptr_adtr1Pk".
  clear -Hnoof_ep_al.
Admitted.

(*
  (* just focus on adtr0 for now. *)
  iClear "His_audit_al1 His_audit_bob1".
  iDestruct (audit_is_my_key with "His_key_al His_audit_al0") as "His_key_al_aud"; [word|].
  iClear "His_key_al".
  destruct is_reg; last first.
  { iNamed "Hreg".
    iDestruct (audit_is_no_other_key with "His_no_key His_audit_bob0") as "His_no_key_aud"; [word|].
    iClear "His_no_key".
    iNamedSuffix "His_key_al_aud" "_al". iNamedSuffix "Haux_al" "_al".
    iNamedSuffix "His_no_key_aud" "_bob".
    iDestruct (mono_list_idx_agree with "Hadtr_map_al Hadtr_map_bob") as %->.
    iDestruct (is_vrf_func (W64 0, W64 0) with "Hhash0_al Hhash_bob") as %->.
    simplify_map_eq/=. }
  wp_apply wp_Assert_true. iNamedSuffix "Hreg" "_bob".
  wp_apply (wp_BytesEqual with "[$Hsl_pk_al $Hsl_pk_bob]"). iIntros "_".
  iDestruct (audit_is_other_key with "His_key_bob His_audit_bob0") as "His_key_bob_aud"; [word|].
  iClear "His_key_bob His_audit_al0 His_audit_bob0".
  iNamedSuffix "His_key_al_aud" "_al".
  iNamedSuffix "His_key_bob_aud" "_bob".
  iDestruct (mono_list_idx_agree with "Hadtr_map_al Hadtr_map_bob") as %->.
  iDestruct (msv_is_my_key with "Haux_al") as (vals0) "[Hmsv0 %Hvals0]".
  iDestruct (msv_is_other_key with "Haux_bob") as (? vals1) "[Hmsv1 %Hvals1]".
  iDestruct (msv_opaque_func (adtr_map0, W64 0) with "Hmsv0 Hmsv1") as %->.
  simplify_eq/=. iDestruct (is_comm_inj with "Hcomm_al Hcomm_bob") as %->.
  wp_apply wp_Assert; [by case_bool_decide|]. wp_pures. by iApply "HΦ".
Qed.
*)

End proof.
