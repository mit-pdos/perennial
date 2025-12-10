From New.generatedproof.github_com.sanjit_bhat.pav Require Import client.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi ktcore safemarshal sigpred.

From New.proof.github_com.sanjit_bhat.pav.client_proof Require Import
  base.

Module client.
Import base.client.

Module evidVrf.
Record t :=
  mk' {
    vrfPk0: list w8;
    sig0: list w8;
    vrfPk1: list w8;
    sig1: list w8;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_vrfPk0 sl_sig0 sl_vrfPk1 sl_sig1,
  "Hstruct" ∷ ptr ↦{d} (client.evidVrf.mk sl_vrfPk0 sl_sig0 sl_vrfPk1 sl_sig1) ∗

  "Hsl_vrfPk0" ∷ sl_vrfPk0 ↦*{d} obj.(vrfPk0) ∗
  "Hsl_sig0" ∷ sl_sig0 ↦*{d} obj.(sig0) ∗
  "Hsl_vrfPk1" ∷ sl_vrfPk1 ↦*{d} obj.(vrfPk1) ∗
  "Hsl_sig1" ∷ sl_sig1 ↦*{d} obj.(sig1).

End proof.
End evidVrf.

Module evidLink.
Record t :=
  mk' {
    epoch: w64;
    link0: list w8;
    sig0: list w8;
    link1: list w8;
    sig1: list w8;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_link0 sl_sig0 sl_link1 sl_sig1,
  "Hstruct" ∷ ptr ↦{d} (client.evidLink.mk obj.(epoch) sl_link0 sl_sig0 sl_link1 sl_sig1) ∗

  "Hsl_link0" ∷ sl_link0 ↦*{d} obj.(link0) ∗
  "Hsl_sig0" ∷ sl_sig0 ↦*{d} obj.(sig0) ∗
  "Hsl_link1" ∷ sl_link1 ↦*{d} obj.(link1) ∗
  "Hsl_sig1" ∷ sl_sig1 ↦*{d} obj.(sig1).

End proof.
End evidLink.

Module Evid.
Record t :=
  mk' {
    vrf: option evidVrf.t;
    link: option evidLink.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ ptr_vrf ptr_link,
  "Hstruct" ∷ ptr ↦{d} (client.Evid.mk ptr_vrf ptr_link) ∗

  "Hown_vrf" ∷
    match obj.(vrf) with
    | Some vrf => evidVrf.own ptr_vrf vrf d
    | None => ⌜ptr_vrf = null⌝
    end ∗
  "Hown_link" ∷
    match obj.(link) with
    | Some link => evidLink.own ptr_link link d
    | None => ⌜ptr_link = null⌝
    end.

End proof.
End Evid.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{pavG Σ}.

Definition wish_evidVrf e pk : iProp Σ :=
  "#Hwish0" ∷ ktcore.wish_VrfSig pk e.(evidVrf.vrfPk0) e.(evidVrf.sig0) ∗
  "#Hwish1" ∷ ktcore.wish_VrfSig pk e.(evidVrf.vrfPk1) e.(evidVrf.sig1) ∗
  "%Heq" ∷ ⌜e.(evidVrf.vrfPk0) ≠ e.(evidVrf.vrfPk1)⌝.

Lemma wish_evidVrf_sig_pred e pk γ :
  wish_evidVrf e pk -∗
  ¬ cryptoffi.is_sig_pk pk (sigpred.pred γ).
Proof.
  iIntros "@ #His_pk".
  iNamedSuffix "Hwish0" "0".
  iNamedSuffix "Hwish1" "1".
  iDestruct (cryptoffi.is_sig_to_pred with "His_pk His_sig0") as "#HP0".
  iDestruct (cryptoffi.is_sig_to_pred with "His_pk His_sig1") as "#HP1".
  iDestruct "HP0" as "[H|H]"; [|by iNamed "H"].
  iNamedSuffix "H" "0".
  iDestruct "HP1" as "[H|H]"; [|by iNamed "H"].
  iNamedSuffix "H" "1".
  remember (ktcore.VrfSig.mk' _ _) as o0 in Henc0.
  remember (ktcore.VrfSig.mk' _ _) as o1 in Henc0.
  opose proof (ktcore.VrfSig.wish_det [] [] o0 o1 _ _) as [? _].
  { by list_simplifier. }
  { rewrite /ktcore.VrfSig.wish.
    list_simplifier.
    intuition.
    by f_equal. }
  remember (ktcore.VrfSig.mk' _ _) as o2 in Henc1.
  remember (ktcore.VrfSig.mk' _ _) as o3 in Henc1.
  opose proof (ktcore.VrfSig.wish_det [] [] o2 o3 _ _) as [? _].
  { by list_simplifier. }
  { rewrite /ktcore.VrfSig.wish.
    list_simplifier.
    intuition.
    by f_equal. }
  iCombine "Hshot0 Hshot1" gives %[_ <-].
  simplify_eq/=.
Qed.

Lemma wp_evidVrf_check ptr_e e sl_pk pk :
  {{{
    is_pkg_init client ∗
    "#Hown_evid" ∷ evidVrf.own ptr_e e (□) ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk
  }}}
  ptr_e @ (ptrT.id client.evidVrf.id) @ "check" #sl_pk
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_evidVrf e pk
      | false =>
        "#Hwish_evidVrf" ∷ wish_evidVrf e pk
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_evid".
  wp_auto.
  wp_apply ktcore.wp_VerifyVrfSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "0".
  wp_apply ktcore.wp_VerifyVrfSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "1".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  iApply "HΦ".
  case_bool_decide.
  - by iIntros "@".
  - by iFrame "#".
Qed.

Definition wish_evidLink e pk : iProp Σ :=
  "#Hwish0" ∷ ktcore.wish_LinkSig pk e.(evidLink.epoch) e.(evidLink.link0) e.(evidLink.sig0) ∗
  "#Hwish1" ∷ ktcore.wish_LinkSig pk e.(evidLink.epoch) e.(evidLink.link1) e.(evidLink.sig1) ∗
  "%Heq" ∷ ⌜e.(evidLink.link0) ≠ e.(evidLink.link1)⌝.

Lemma wish_evidLink_sig_pred e pk γ :
  wish_evidLink e pk -∗
  ¬ cryptoffi.is_sig_pk pk (sigpred.pred γ).
Proof.
  iIntros "@ #His_pk".
  destruct e. simpl in *.
  iNamedSuffix "Hwish0" "0".
  iNamedSuffix "Hwish1" "1".
  iDestruct (cryptoffi.is_sig_to_pred with "His_pk His_sig0") as "#HP0".
  iDestruct (cryptoffi.is_sig_to_pred with "His_pk His_sig1") as "#HP1".
  iDestruct "HP0" as "[H|H]"; [by iNamed "H"|].
  iNamedSuffix "H" "0".
  iDestruct "HP1" as "[H|H]"; [by iNamed "H"|].
  iNamedSuffix "H" "1".
  remember (ktcore.LinkSig.mk' _ _ _) as o0 in Henc0.
  remember (ktcore.LinkSig.mk' _ _ _) as o1 in Henc0.
  opose proof (ktcore.LinkSig.wish_det [] [] o0 o1 _ _) as [? _].
  { by list_simplifier. }
  { rewrite /ktcore.LinkSig.wish.
    list_simplifier.
    intuition.
    by f_equal. }
  remember (ktcore.LinkSig.mk' _ _ _) as o2 in Henc1.
  remember (ktcore.LinkSig.mk' _ _ _) as o3 in Henc1.
  opose proof (ktcore.LinkSig.wish_det [] [] o2 o3 _ _) as [? _].
  { by list_simplifier. }
  { rewrite /ktcore.LinkSig.wish.
    list_simplifier.
    intuition.
    by f_equal. }
  simplify_eq/=.
  iCombine "Hshot0 Hshot1" gives %[_ <-].
  iDestruct (mono_list_idx_own_get with "Hlb0") as "Hidx0"; [done|].
  iDestruct (mono_list_idx_own_get with "Hlb1") as "Hidx1"; [done|].
  iDestruct (mono_list_idx_agree with "Hidx0 Hidx1") as %->.
  done.
Qed.

Lemma wp_evidLink_check ptr_e e sl_pk pk :
  {{{
    is_pkg_init client ∗
    "#Hown_evid" ∷ evidLink.own ptr_e e (□) ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk
  }}}
  ptr_e @ (ptrT.id client.evidLink.id) @ "check" #sl_pk
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_evidLink e pk
      | false =>
        "#Hwish_evidLink" ∷ wish_evidLink e pk
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_evid".
  wp_auto.
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "0".
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "1".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  iApply "HΦ".
  case_bool_decide.
  - by iIntros "@".
  - by iFrame "#".
Qed.

Definition wish_Evid e pk : iProp Σ :=
  match e.(Evid.vrf), e.(Evid.link) with
  | Some e', None => wish_evidVrf e' pk
  | None, Some e' => wish_evidLink e' pk
  | _, _ => False
  end.

Lemma wish_Evid_sig_pred e pk γ :
  wish_Evid e pk -∗
  ¬ cryptoffi.is_sig_pk pk (sigpred.pred γ).
Proof.
  iIntros "#Hwish #His_pk".
  destruct e.
  destruct vrf as [vrf|], link as [link|]; try done.
  - iNamed "Hwish".
    iApply (wish_evidVrf_sig_pred vrf); [|done].
    by iFrame "#".
  - iNamed "Hwish".
    iApply (wish_evidLink_sig_pred link); [|done].
    by iFrame "#".
Qed.

Lemma wp_Evid_Check ptr_e e sl_pk pk :
  {{{
    is_pkg_init client ∗
    "#Hown_evid" ∷ Evid.own ptr_e e (□) ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk
  }}}
  ptr_e @ (ptrT.id client.Evid.id) @ "Check" #sl_pk
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_Evid e pk
      | false =>
        "#Hwish_Evid" ∷ wish_Evid e pk
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_evid".
  wp_auto.
  destruct e. simpl.

  wp_if_destruct.
  2: {
    destruct vrf.
    2: { by iDestruct "Hown_vrf" as %?. }
    wp_if_destruct.
    2: {
      destruct link.
      2: { by iDestruct "Hown_link" as %?. }
      by iApply "HΦ". }
    destruct link.
    { iNamedSuffix "Hown_link" "'".
      by iDestruct (typed_pointsto_not_null with "Hstruct'") as %?. }
    wp_apply wp_evidVrf_check as "* @".
    { iFrame "#". }
    by iApply "HΦ". }

  destruct vrf.
  { iNamedSuffix "Hown_vrf" "'".
    by iDestruct (typed_pointsto_not_null with "Hstruct'") as %?. }
  wp_if_destruct.
  { destruct link.
    { iNamedSuffix "Hown_link" "'".
      by iDestruct (typed_pointsto_not_null with "Hstruct'") as %?. }
    by iApply "HΦ". }
  destruct link.
  2: { by iDestruct "Hown_link" as %?. }
  wp_apply wp_evidLink_check as "* @".
  { iFrame "#". }
  by iApply "HΦ".
Qed.

End proof.
End client.
