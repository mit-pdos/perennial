From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc auditor core classes client cryptoffi evidence
  logical_audit merkle msv rpc serde server.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_hist c γaudit hist : iProp Σ :=
  "%Hnil_hist" ∷ ⌜ hist = [] → c.(Client.next_ver) = (W64 0) ⌝ ∗
  "%Hhist_len" ∷ ⌜ Z.of_nat (length hist) = uint.Z c.(Client.next_epoch) ⌝ ∗
  (* for all epochs, msv. *)
  "#Hall_hist" ∷ (∀ ep opt_pk,
    ⌜ hist !! (uint.nat ep) = Some opt_pk ⌝ -∗
    msv γaudit c.(Client.serv).(Server.vrf_pk) ep c.(Client.uid) opt_pk) ∗
  (* for last epoch, msv with associated n_vers. *)
  "#Hlast_hist" ∷ (∀ opt_pk,
    ⌜ last hist = Some opt_pk ⌝ -∗
    msv_vers γaudit c.(Client.serv).(Server.vrf_pk)
      (W64 (length hist - 1)) c.(Client.uid) opt_pk c.(Client.next_ver)).

Lemma wp_ClientHist__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hcli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (bound_ep : w64) ptr_err, RET (#bound_ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(Client.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ Client.own ptr_c c
      else
        ∃ next_ver next_ep,
        let new_c := set Client.next_ver (λ _, next_ver)
          (set Client.next_epoch (λ _, next_ep) c) in
        "Hcli" ∷ Client.own ptr_c new_c ∗

        "#Hhist_updater" ∷ (□ ∀ γaudit audit_ep,
          ⌜ uint.Z next_ep <= uint.Z audit_ep ⌝ -∗
          logical_audit c.(Client.γ) γaudit c.(Client.serv).(Server.vrf_pk) audit_ep -∗

          (* can't put old_hist in precond.
          it'd be under existential (see below),
          so we couldn't reference / extend it in new_hist.
          instead, need this "updater"-style, which is more clunky to use. *)
          ∀ old_hist,
          is_hist c γaudit old_hist -∗

          (* ∃ insert_ep must come after logical_audit bc it's derived
          from the auditor's monotonicity invariant. *)
          ∃ (insert_ep : w64),
          let last_len := uint.Z insert_ep - Z.of_nat (length old_hist) in
          let new_len := uint.Z bound_ep - uint.Z insert_ep + 1 in
          let new_hist := old_hist ++
            replicate (Z.to_nat last_len) (mjoin $ last old_hist) ++
            replicate (Z.to_nat new_len) (Some pk) in
          ⌜ Z.of_nat (length old_hist) <= uint.Z insert_ep <= uint.Z bound_ep ⌝ ∗
          ⌜ uint.Z $ word.add bound_ep (W64 1) = (uint.Z bound_ep + 1)%Z ⌝ ∗
          is_hist new_c γaudit new_hist))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H".
  destruct c. simpl.
  wp_apply (wp_Client__Put with "[$Hcli $Hsl_pk]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; [by iFrame "∗#"|].
  iFrame.

  iIntros "!> * % #Haudit *".
  iNamedSuffix 1 "_old". simpl in *.
  destruct (last old_hist) eqn:Heq_last.
  2: {
    iClear "Hall_hist_old Hlast_hist_old".
    apply last_None in Heq_last as ->.
    opose proof (Hnil_hist_old _) as ->; [done|].
    iNamed "Haudit".
Admitted.

Lemma wp_ClientHist__SelfMon ptr_c c :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        let new_len := uint.Z ep + 1 in
        let len_diff := new_len - Z.of_nat (length c.(ClientHist.epochs_hist)) in
        let new_c := set ClientHist.epochs_hist (λ x, x ++
          replicate (Z.to_nat len_diff) (mjoin $ last x)) c in
        "%Hlt_diff" ∷ ⌜ len_diff >= 0 ⌝ ∗
        "%Hnoof_ep" ∷ ⌜ new_len = uint.Z $ word.add ep (W64 1) ⌝ ∗
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__SelfMon with "[$Hcli]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; [by iFrame "∗#"|].
  iSplit; [word|].
  iSplit; [word|].
  iExists puts_hist, (word.add ep (W64 1)).
  do 3 try iSplit; simpl in *.
  - rewrite !length_app length_replicate. word.
  - iPureIntro.
    by apply hist_epochs_puts.update_replicate.
  - iFrame.
  - iApply (hist_extend_selfmon with "[$Hhist $His_selfmon_post]"); word.
Qed.

End proof.

Global Typeclasses Opaque ClientHist.own.
