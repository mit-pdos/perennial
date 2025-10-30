From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From Perennial.Helpers Require Import NamedProps.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi cryptoutil.

From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import
  serde.

Module ktcore.
Import serde.ktcore.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Inductive Blame :=
  | BlameServSig
  | BlameServFull
  | BlameAdtrSig
  | BlameAdtrFull
  | BlameClients
  | BlameUnknown.

Lemma wp_SignVrf ptr_sk pk P sl_vrfPk vrfPk :
  let enc := VrfSig.pure_enc (VrfSig.mk' (W8 VrfSigTag) vrfPk) in
  {{{
    is_pkg_init ktcore ∗
    "#His_sig_sk" ∷ cryptoffi.is_sig_sk ptr_sk pk P ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "HP" ∷ P enc
  }}}
  @! ktcore.SignVrf #ptr_sk #sl_vrfPk
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#His_sig" ∷ cryptoffi.is_sig pk enc sig
  }}}.
Proof.
  simpl. wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&Hown&%Hwish)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPrivateKey_Sign with "[$Hsl_b $HP]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_VerifyVrfSig (pk' : cryptoffi.SigPublicKey.t) pk sl_vrfPk vrfPk sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! ktcore.VerifyVrfSig #pk' #sl_vrfPk #sl_sig
  {{{
    (err : bool), RET #err;
    let enc := VrfSig.pure_enc (VrfSig.mk' (W8 VrfSigTag) vrfPk) in
    "Hgenie" ∷
      match err with
      | true => ¬ cryptoffi.is_sig pk enc sig
      | false =>
        "#His_sig" ∷ cryptoffi.is_sig pk enc sig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&Hown&%Hwish)".
  { iFrame "#". }
  simpl in *.
Admitted.

Lemma wp_SignLink ptr_sk (epoch : w64) sl_link link :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_link" ∷ sl_link ↦* link
  }}}
  @! ktcore.SignLink #ptr_sk #epoch #sl_link
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_link" ∷ sl_link ↦* link ∗
    "Hsl_sig" ∷ sl_sig ↦* sig
  }}}.
Proof. Admitted.

Lemma wp_VerifyLinkSig pk (epoch : w64) sl_link link sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_link" ∷ sl_link ↦* link ∗
    "Hsl_sig" ∷ sl_sig ↦* sig
  }}}
  @! ktcore.VerifyLinkSig pk #epoch #sl_link #sl_sig
  {{{
    (err : bool), RET #err;
    "Hsl_link" ∷ sl_link ↦* link ∗
    "Hsl_sig" ∷ sl_sig ↦* sig
  }}}.
Proof. Admitted.

Lemma wp_ProveMapLabel (uid ver : w64) ptr_sk :
  {{{
    is_pkg_init ktcore
  }}}
  @! ktcore.ProveMapLabel #uid #ver #ptr_sk
  {{{
    sl_label label sl_proof proof, RET (#sl_label, #sl_proof);
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hsl_proof" ∷ sl_proof ↦* proof
  }}}.
Proof. Admitted.

Lemma wp_EvalMapLabel (uid ver : w64) ptr_sk :
  {{{
    is_pkg_init ktcore
  }}}
  @! ktcore.EvalMapLabel #uid #ver #ptr_sk
  {{{
    sl_label label, RET #sl_label;
    "Hsl_label" ∷ sl_label ↦* label
  }}}.
Proof. Admitted.

Lemma wp_CheckMapLabel ptr_pk (uid ver : w64) sl_proof proof :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_proof" ∷ sl_proof ↦* proof
  }}}
  @! ktcore.CheckMapLabel #ptr_pk #uid #ver #sl_proof
  {{{
    sl_label label (err : bool), RET (#sl_label, #err);
    "Hsl_proof" ∷ sl_proof ↦* proof ∗
    "Hsl_label" ∷ sl_label ↦* label
  }}}.
Proof. Admitted.

Lemma wp_GetMapVal ptr_pkOpen :
  {{{
    is_pkg_init ktcore
  }}}
  @! ktcore.GetMapVal #ptr_pkOpen
  {{{
    sl_val val, RET #sl_val;
    "Hsl_val" ∷ sl_val ↦* val
  }}}.
Proof. Admitted.

Lemma wp_GetCommitRand sl_commitSecret commitSecret sl_label label :
  {{{
    is_pkg_init ktcore ∗
    "Hsl_commitSecret" ∷ sl_commitSecret ↦* commitSecret ∗
    "Hsl_label" ∷ sl_label ↦* label
  }}}
  @! ktcore.GetCommitRand #sl_commitSecret #sl_label
  {{{
    sl_rand rand, RET #sl_rand;
    "Hsl_commitSecret" ∷ sl_commitSecret ↦* commitSecret ∗
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hsl_rand" ∷ sl_rand ↦* rand
  }}}.
Proof. Admitted.

End proof.
End ktcore.
