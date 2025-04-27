From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc agreement auditor core classes client cryptoffi
  evidence logical_audit merkle rpc serde server.

Module ClientHist.
Record t :=
  mk {
    γ: gname;
    uid: w64;
    (* pks differs from the client struct.
    it tracks all our actual keys. *)
    pks: list map_val_ty;
    next_epoch: w64;
    (* hist_epoch differs from the client struct.
    it's epoch validity for the history, which only gets updated by
    Put and SelfMon, not Get. *)
    hist_epoch: w64;
    serv: Server.t;
    serv_is_good: bool;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; pks; next_epoch; hist_epoch; serv; serv_is_good>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  "%Hlt_ep" ∷ ⌜ uint.Z obj.(hist_epoch) <= uint.Z obj.(next_epoch) ⌝ ∗
  "Hcli" ∷ Client.own ptr (Client.mk obj.(γ) obj.(uid) (W64 $ length obj.(pks))
    obj.(next_epoch) obj.(serv) obj.(serv_is_good)) ∗
  "#Hhist" ∷ is_hist obj.(γ) obj.(serv).(Server.vrf_pk) obj.(uid) obj.(pks) obj.(hist_epoch).

End defs.
End ClientHist.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_ClientHist__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗
    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        let new_c := set ClientHist.pks (λ x, (x ++ [(ep, pk)]))
          (set ClientHist.next_epoch (λ _, word.add ep (W64 1))
          (set ClientHist.hist_epoch (λ _, word.add ep (W64 1)) c)) in
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__Put with "[$Hcli $Hsl_pk]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; [by iFrame "∗#"|].
  iSplit; simpl in *; [done|]; iSplit.
  - rewrite length_app. simpl.
    replace (W64 (_ + _)%nat) with
      (word.add (W64 $ length pks) (W64 1)); [|word].
    iFrame.
  - iApply hist_extend_put; [..|iFrame "#"]; try word.
Qed.

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
        let new_c := set ClientHist.next_epoch (λ _, word.add ep (W64 1))
          (set ClientHist.hist_epoch (λ _, word.add ep (W64 1)) c) in
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__SelfMon with "[$Hcli]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; iFrame "∗#"; simpl; [done|].
  iSplit; [done|].
  (* TODO: maybe iApply bug. this doesn't work.
  iApply (hist_extend_selfmon with "[# $]"). *)
  iApply hist_extend_selfmon; [..|iFrame "#"]; word.
Qed.

Lemma wp_ClientHist__Get ptr_c c (uid : w64) :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    err sl_pk (is_reg : bool) (ep : w64) ptr_err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        let new_c := set ClientHist.next_epoch (λ _, word.add ep (W64 1)) c in
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  wp_apply (wp_Client__Get with "[$Hcli]").
  simpl. iIntros "*". iNamed 1.
  iApply "HΦ". iFrame "∗%".
  case_match; iNamed "Herr"; iFrame "∗#"; simpl; [done|word].
Qed.

End proof.
