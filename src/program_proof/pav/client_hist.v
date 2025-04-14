From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc auditor core classes client cryptoffi evidence
  history merkle rpc serde server.

Module ClientHist.
Record t :=
  mk {
    γ: gname;
    uid: w64;
    (* pks is the only difference from normal client struct. *)
    pks: list map_val_ty;
    ep_valid: w64;
    serv: Server.t;
    serv_is_good: bool;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; pks; ep_valid; serv; serv_is_good>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  "Hcli" ∷ Client.own ptr (Client.mk obj.(γ) obj.(uid) (W64 $ length obj.(pks))
    obj.(ep_valid) obj.(serv) obj.(serv_is_good)) ∗
  "#Hhist" ∷ is_hist obj.(γ) obj.(serv).(Server.vrf_pk) obj.(uid) obj.(pks) obj.(ep_valid).

End defs.
End ClientHist.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hcli" ∷ ClientHist.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    let new_c := set ClientHist.pks (λ x, (x ++ [(ep, pk)]))
      (set ClientHist.ep_valid (λ _, word.add ep (W64 1)) c) in
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(ClientHist.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(ClientHist.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗
    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hcli" ∷ ClientHist.own ptr_c c
      else
        "Hcli" ∷ ClientHist.own ptr_c new_c)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hcli".
  destruct c. simpl in *.
  destruct serv_is_good eqn:Heq_good.
  - wp_apply (wp_Client__Put_good with "[$Hcli $Hsl_pk //]").
    iIntros "*". iNamed 1. simpl in *.
    iApply "HΦ". iFrame. iSplit; [done|].
    rewrite Herr. iSplit; simpl in *.
    { rewrite length_app. simpl.
      replace (W64 (_ + _)%nat) with
        (word.add (W64 $ length pks) (W64 1)); [|word].
      iFrame. }
    iApply (hist_extend_put with "[$Hhist $His_put_post]"); word.
  - wp_apply (wp_Client__Put with "[$Hcli $Hsl_pk //]").
    iIntros "*". iNamed 1. simpl in *.
    iApply "HΦ". iFrame. iSplit; [done|].
    case_match; [iFrame "∗#"|]. iNamed "Herr".
    iSplit; simpl in *.
    { rewrite length_app. simpl.
      replace (W64 (_ + _)%nat) with
        (word.add (W64 $ length pks) (W64 1)); [|word].
      iFrame. }
    iApply (hist_extend_put with "[$Hhist $His_put_post]"); word.
Qed.

(* parallel with normal audit is hist_audit_msv. *)
Lemma logical_audit (ep : w64) ptr_c c :
  c.(ClientHist.serv_is_good) = true →
  uint.Z ep < uint.Z c.(ClientHist.ep_valid) →
  ClientHist.own ptr_c c -∗
  msv c.(ClientHist.serv).(Server.γhist) ep c.(ClientHist.uid)
    (get_lat c.(ClientHist.pks) ep).
Proof. Admitted.

End proof.
