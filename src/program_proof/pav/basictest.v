From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import advrpc auditor core client rpc server.
From Perennial.program_proof Require Import std_proof.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_testBasic (servAddr adtr0Addr adtr1Addr : w64) :
  {{{ True }}}
  testBasic #servAddr #adtr0Addr #adtr1Addr
  {{{ RET #(); True }}}.
Proof.
  rewrite /testBasic.
  iIntros (Φ) "_ HΦ".

  (* set up server and auditors. *)
  wp_apply wp_newServer. iIntros (????). iNamed 1.
  wp_pures.
  wp_apply (wp_newRpcServer with "Hown_serv"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_newAuditor. iIntros (?????). iNamedSuffix 1 "0".
  wp_apply (wp_newRpcAuditor with "[$Hown_adtr0]"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_newAuditor. iIntros (?????). iNamedSuffix 1 "1".
  wp_apply (wp_newRpcAuditor with "[$Hown_adtr1]"). iIntros (??). iNamed 1.
  wp_apply (wp_Server__Serve with "Hown_rpcserv").
  wp_apply wp_Sleep.

  (* alice put. *)
  wp_apply wp_newClient. iIntros (??????). iNamedSuffix 1 "_al".
  wp_apply wp_SliceSingleton; [val_ty|]. iIntros (?) "Hpk0".
  iDestruct (slice.own_slice_to_small with "Hpk0") as "Hpk0".
  wp_apply (wp_Client__Put with "[$Hown_cli_al Hpk0]").
  { instantiate (1:=[_]). iFrame "Hpk0". }
  iIntros (ep0 ? err0) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err0.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al".

  (* update auditors. *)
  wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "0".
  wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "1".
  wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "2".
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
  wp_apply wp_newClient. iIntros (??????). iNamedSuffix 1 "_bob".
  wp_apply (wp_Client__Get with "Hown_cli_bob").
  iIntros (is_reg ?? ep1 ? err7) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err7.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_". wp_apply wp_Assume. iIntros "%Heq_ep /=".
  iNamedSuffix "H" "_bob". iRename "H" into "Hreg".

  (* alice and bob audit. *)
  wp_apply (wp_Client__Audit with "[$Hown_cli_al $Hsl_adtrPk0 $His_adtrPk0]").
  iIntros (? err8) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err8.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al0".
  wp_apply (wp_Client__Audit with "[$Hown_cli_al $Hsl_adtrPk1 $His_adtrPk1]").
  iIntros (? err9) "H /=". iNamedSuffix "H" "_al".
  wp_loadField. iClear "Herr_al". destruct err9.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_al1".
  wp_apply (wp_Client__Audit with "[$Hown_cli_bob $Hsl_adtrPk0 $His_adtrPk0]").
  iIntros (? err10) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err10.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_bob0".
  wp_apply (wp_Client__Audit with "[$Hown_cli_bob $Hsl_adtrPk1 $His_adtrPk1]").
  iIntros (? err11) "H /=". iNamedSuffix "H" "_bob".
  wp_loadField. iClear "Herr_bob". destruct err11.(clientErr.err).
  { wp_apply wp_Assume_false. }
  wp_apply wp_Assume. iIntros "_ /=". iNamedSuffix "H" "_bob1".

  (* main part: proving the pk's are equal. *)
  iClear "Hsl_adtrPk0 His_adtrPk0 Hsl_adtrPk1 His_adtrPk1 Hown_cli0
    Hown_cli1 Hown_cli2 Hown_upd0 Hown_upd1 Hown_cli_al Hown_cli_bob".
  case_bool_decide; [|done]. simplify_eq/=.
Admitted.

End proof.
