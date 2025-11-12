From New.generatedproof.github_com.sanjit_bhat.pav Require Import auditor.

From New.proof Require Import bytes sync.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc cryptoffi hashchain ktcore merkle server.

From New.proof.github_com.sanjit_bhat.pav.auditor_proof Require Import
  base.

(* TODO: bad New.proof.sync exports.
https://github.com/mit-pdos/perennial/issues/470 *)
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module auditor.
Import base.auditor.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition wish_CheckStart servPk reply (ep : w64) dig link : iProp Σ :=
  ∃ digs0 digs1 cut,
  (* hashchain. *)
  "%Hlen_link_prev" ∷ ⌜Z.of_nat $ length reply.(server.StartReply.PrevLink) = cryptoffi.hash_len⌝ ∗
  "#His_chain_prev" ∷ hashchain.is_chain digs0 cut reply.(server.StartReply.PrevLink)
    (uint.nat reply.(server.StartReply.PrevEpochLen)) ∗
  "%Hwish_chain" ∷ ⌜hashchain.wish_Verify reply.(server.StartReply.ChainProof) digs1⌝ ∗
  "#His_chain_start" ∷ hashchain.is_chain (digs0 ++ digs1) cut link
    (uint.nat reply.(server.StartReply.PrevEpochLen) + length digs1) ∗
  "%Heq_ep" ∷ ⌜uint.Z reply.(server.StartReply.PrevEpochLen) + length digs1 - 1 = uint.Z ep⌝ ∗
  "%Heq_dig" ∷ ⌜last digs1 = Some dig⌝ ∗
  "#His_link_sig" ∷ ktcore.wish_VerifyLinkSig servPk ep link reply.(server.StartReply.LinkSig) ∗

  (* vrf. *)
  "#His_vrf_pk" ∷ cryptoffi.is_vrf_pk reply.(server.StartReply.VrfPk) ∗
  "#His_vrf_sig" ∷ ktcore.wish_VerifyVrfSig servPk reply.(server.StartReply.VrfPk)
    reply.(server.StartReply.VrfSig).

Lemma wish_CheckStart_det pk r e0 e1 d0 d1 l0 l1 :
  wish_CheckStart pk r e0 d0 l0 -∗
  wish_CheckStart pk r e1 d1 l1 -∗
  ⌜e0 = e1 ∧ d0 = d1 ∧ l0 = l1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (hashchain.is_chain_inj with "His_chain_prev0 His_chain_prev1") as %[-> ->].
  opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain0 Hwish_chain1) as ->.
  iDestruct (hashchain.is_chain_det with "His_chain_start0 His_chain_start1") as %->.
  iPureIntro.
  rewrite Heq_dig0 in Heq_dig1.
  rewrite Heq_ep0 in Heq_ep1.
  by simplify_eq/=.
Qed.

Lemma wp_CheckStart sl_servPk servPk ptr_reply reply :
  {{{
    is_pkg_init auditor ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hown_reply" ∷ server.StartReply.own ptr_reply reply (□)
  }}}
  @! auditor.CheckStart #sl_servPk #ptr_reply
  {{{
    (ep : w64) sl_dig sl_link ptr_vrfPk (err : bool),
    RET (#ep, #sl_dig, #sl_link, #ptr_vrfPk, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ ep dig link, wish_CheckStart servPk reply ep dig link
      | false =>
        ∃ dig link,
        "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
        "#Hsl_link" ∷ sl_link ↦*□ link ∗
        "#Hwish_CheckStart" ∷ wish_CheckStart servPk reply ep dig link ∗
        "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_vrfPk reply.(server.StartReply.VrfPk)
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_reply". destruct reply. simpl.
  wp_auto.
  iDestruct (own_slice_len with "Hsl_PrevLink") as %[? _].
  wp_if_destruct.
  2: { iApply "HΦ". iIntros "@". simpl in *. word. }
  iDestruct (hashchain.is_chain_invert PrevLink (uint.nat PrevEpochLen))
    as "(%&%&#His_chain_prev)"; [word|].
  wp_apply (hashchain.wp_Verify with "[$His_chain_prev]") as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. iApply "Hgenie". naive_solver. }
  iNamed "Hgenie".
  iPersist "Hsl_newVal Hsl_newLink".
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *.
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    apply last_Some in Heq_dig' as [? Heq].
    apply (f_equal length) in Heq.
    autorewrite with len in *.
    word. }
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { iApply "HΦ". iNamedSuffix 1 "'". simpl in *.
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    word. }
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. iApply "Hgenie".
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    iDestruct (hashchain.is_chain_inj with "His_chain_prev His_chain_prev'") as %[-> ->].
    iDestruct (hashchain.is_chain_det with "His_chain His_chain_start'") as %->.
    iExactEq "His_link_sig'". repeat f_equal. word. }
  iNamed "Hgenie".
  wp_apply cryptoffi.wp_VrfPublicKeyDecode as "* @ {Hsl_enc}".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. by iApply "Hgenie". }
  iNamed "Hgenie".
  wp_apply ktcore.wp_VerifyVrfSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. by iApply "Hgenie". }
  iNamed "Hgenie".

  iDestruct (cryptoffi.own_vrf_pk_valid with "Hown_vrf_pk") as "#His_vrf_pk".
  iDestruct (hashchain.is_chain_hash_len with "His_chain_prev") as %?.
  iApply "HΦ".
  iFrame "#%". simpl in *.
  iPureIntro. split; [word|].
  destruct (last _) eqn:Heq; [done|].
  apply last_None in Heq.
  apply (f_equal length) in Heq.
  simpl in *. word.
Qed.

End proof.
End auditor.
