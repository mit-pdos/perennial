From New.generatedproof.github_com.sanjit_bhat.pav Require Import ktcore.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi cryptoutil merkle.

From New.proof.github_com.sanjit_bhat.pav.ktcore_proof Require Import
  serde.

Module ktcore.
Import serde.ktcore.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Inductive BlameTys :=
  | BlameServSig
  | BlameServFull
  | BlameAdtrSig
  | BlameAdtrFull
  | BlameClients
  | BlameUnknown.

Axiom BlameTys_EqDecision : EqDecision BlameTys.
Global Existing Instance BlameTys_EqDecision.

Axiom BlameTys_Countable : Countable BlameTys.
Global Existing Instance BlameTys_Countable.

Definition Blame := gset BlameTys.

Axiom Blame_IntoVal : IntoVal Blame.
Global Existing Instance Blame_IntoVal.

Definition wish_VrfSig pk vrfPk sig : iProp Σ :=
  let obj := VrfSig.mk' (W8 VrfSigTag) vrfPk in
  let enc := VrfSig.pure_enc obj in
  "#His_sig" ∷ cryptoffi.is_sig pk enc sig ∗
  "%Hvalid" ∷ ⌜VrfSig.valid obj⌝.

Lemma wp_SignVrf ptr_sk pk P sl_vrfPk vrfPk :
  let enc := VrfSig.pure_enc (VrfSig.mk' (W8 VrfSigTag) vrfPk) in
  {{{
    is_pkg_init ktcore ∗
    "#Hown_sig_sk" ∷ cryptoffi.own_sig_sk ptr_sk pk P ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "HP" ∷ P enc
  }}}
  @! ktcore.SignVrf #ptr_sk #sl_vrfPk
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#Hwish_vrfSig" ∷ wish_VrfSig pk vrfPk sig
  }}}.
Proof.
  simpl. wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPrivateKey_Sign with "[$Hsl_b $HP]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_VerifyVrfSig sl_pk pk sl_vrfPk vrfPk sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ vrfPk ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! ktcore.VerifyVrfSig #sl_pk #sl_vrfPk #sl_sig
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_VrfSig pk vrfPk sig
      | false =>
        "#Hwish_vrfSig" ∷ wish_VrfSig pk vrfPk sig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (VrfSig.wp_enc (VrfSig.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPublicKey_Verify with "[Hsl_b]") as "* H".
  { iFrame "∗#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  destruct err.
  - iIntros "@". by iApply "Hgenie0".
  - by iFrame.
Qed.

Definition wish_LinkSig pk ep link sig : iProp Σ :=
  let obj := LinkSig.mk' (W8 LinkSigTag) ep link in
  let enc := LinkSig.pure_enc obj in
  "#His_sig" ∷ cryptoffi.is_sig pk enc sig ∗
  "%Hvalid" ∷ ⌜LinkSig.valid obj⌝.

Lemma wp_SignLink ptr_sk pk P epoch sl_link link :
  let enc := LinkSig.pure_enc (LinkSig.mk' (W8 LinkSigTag) epoch link) in
  {{{
    is_pkg_init ktcore ∗
    "#Hown_sig_sk" ∷ cryptoffi.own_sig_sk ptr_sk pk P ∗
    "#Hsl_link" ∷ sl_link ↦*□ link ∗
    "HP" ∷ P enc
  }}}
  @! ktcore.SignLink #ptr_sk #epoch #sl_link
  {{{
    sl_sig sig, RET #sl_sig;
    "Hsl_sig" ∷ sl_sig ↦* sig ∗
    "#Hwish_linkSig" ∷ wish_LinkSig pk epoch link sig
  }}}.
Proof.
  simpl. wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  wp_apply (LinkSig.wp_enc (LinkSig.mk' _ _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPrivateKey_Sign with "[$Hsl_b $HP]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  by iFrame "∗#".
Qed.

Lemma wp_VerifyLinkSig sl_pk pk epoch sl_link link sl_sig sig :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#Hsl_link" ∷ sl_link ↦*□ link ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! ktcore.VerifyLinkSig #sl_pk #epoch #sl_link #sl_sig
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_LinkSig pk epoch link sig
      | false =>
        "#Hwish_linkSig" ∷ wish_LinkSig pk epoch link sig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (LinkSig.wp_enc (LinkSig.mk' _ _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_&(_&%Hvalid))".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_SigPublicKey_Verify with "[Hsl_b]") as "* H".
  { iFrame "∗#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  destruct err.
  - iIntros "@". by iApply "Hgenie0".
  - by iFrame.
Qed.

Lemma wp_ProveMapLabel ptr_sk pk (uid ver : w64) :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_sk" ∷ cryptoffi.own_vrf_sk ptr_sk pk
  }}}
  @! ktcore.ProveMapLabel #ptr_sk #uid #ver
  {{{
    sl_label label sl_proof proof, RET (#sl_label, #sl_proof);
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hsl_proof" ∷ sl_proof ↦* proof ∗
    "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc proof ∗
    "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPrivateKey_Prove with "[$Hsl_b]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_EvalMapLabel ptr_sk pk (uid ver : w64) :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_sk" ∷ cryptoffi.own_vrf_sk ptr_sk pk
  }}}
  @! ktcore.EvalMapLabel #ptr_sk #uid #ver
  {{{
    sl_label label, RET #sl_label;
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPrivateKey_Evaluate with "[$Hsl_b]") as "* @".
  { iFrame "#". }
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_CheckMapLabel ptr_pk pk (uid ver : w64) sl_proof proof :
  {{{
    is_pkg_init ktcore ∗
    "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_pk pk ∗
    "#Hsl_proof" ∷ sl_proof ↦*□ proof
  }}}
  @! ktcore.CheckMapLabel #ptr_pk #uid #ver #sl_proof
  {{{
    sl_label label (err : bool), RET (#sl_label, #err);
    let enc := MapLabel.pure_enc (MapLabel.mk' uid ver) in
    "Hsl_label" ∷ sl_label ↦* label ∗
    "Hgenie" ∷
      match err with
      | true => ¬ cryptoffi.is_vrf_proof pk enc proof
      | false =>
        "#His_proof" ∷ cryptoffi.is_vrf_proof pk enc proof ∗
        "#His_out" ∷ cryptoffi.is_vrf_out pk enc label
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_slice_make3 as "* (Hsl_b&Hcap_b&_)"; [word|].
  wp_apply wp_alloc as "* Hstruct".
  iPersist "Hstruct".
  replace (sint.nat _) with (0%nat) by word.
  wp_apply (MapLabel.wp_enc (MapLabel.mk' _ _) with "[$Hsl_b $Hcap_b]")
    as "* (Hsl_b&Hcap_b&_)".
  { iFrame "#". }
  simpl in *.
  wp_apply (cryptoffi.wp_VrfPublicKey_Verify with "[$Hsl_b]") as "* H".
  { iFrame "#". }
  iNamedSuffix "H" "0".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_GetMapVal ptr_pkOpen pkOpen :
  {{{
    is_pkg_init ktcore ∗
    "#Hown" ∷ CommitOpen.own ptr_pkOpen pkOpen (□)
  }}}
  @! ktcore.GetMapVal #ptr_pkOpen
  {{{
    sl_MapVal MapVal, RET #sl_MapVal;
    let enc := CommitOpen.pure_enc pkOpen in
    "Hsl_MapVal" ∷ sl_MapVal ↦* MapVal ∗
    "#His_MapVal" ∷ cryptoffi.is_hash (Some enc) MapVal
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply (CommitOpen.wp_enc (CommitOpen.mk' _ _) with "[$Hown]")
    as "* (Hsl_b&Hcap_b&_)".
  { iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". }
  simpl in *.
  wp_apply (cryptoutil.wp_Hash with "[$Hsl_b]") as "* @".
  iApply "HΦ".
  iFrame "∗#".
Qed.

Lemma wp_GetCommitRand sl_commitSecret commitSecret sl_label label :
  {{{
    is_pkg_init ktcore ∗
    "#Hsl_commitSecret" ∷ sl_commitSecret ↦*□ commitSecret ∗
    "#Hsl_label" ∷ sl_label ↦*□ label
  }}}
  @! ktcore.GetCommitRand #sl_commitSecret #sl_label
  {{{
    sl_rand rand, RET #sl_rand;
    let enc := commitSecret ++ label in
    "Hsl_rand" ∷ sl_rand ↦* rand ∗
    "#His_CommitRand" ∷ cryptoffi.is_hash (Some enc) rand
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply cryptoffi.wp_NewHasher as "* @".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr]") as "H".
  { iFrame "#". }
  iNamedSuffix "H" "0".
  wp_apply (cryptoffi.wp_Hasher_Write with "[$Hown_hr0]") as "H".
  { iFrame "#". }
  iNamedSuffix "H" "1".
  wp_apply (cryptoffi.wp_Hasher_Sum with "[$Hown_hr1]") as "* @".
  { iDestruct own_slice_nil as "$". }
  simpl.
  iApply "HΦ".
  iFrame "∗#".
Qed.

Definition wish_Memb pk uid ver dig memb : iProp Σ :=
  ∃ label mapVal,
  let enc_label := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  let enc_val := ktcore.CommitOpen.pure_enc memb.(ktcore.Memb.PkOpen) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc_label memb.(ktcore.Memb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc_label label ∗
  "#His_mapVal" ∷ cryptoffi.is_hash (Some enc_val) mapVal ∗
  "#Hwish_memb" ∷ merkle.wish_Memb label mapVal memb.(ktcore.Memb.MerkleProof) dig.

Definition wish_ListMemb pk uid (prefixLen : w64) dig hist : iProp Σ :=
  ([∗ list] ver ↦ memb ∈ hist,
    wish_Memb pk uid (uint.Z prefixLen + ver) dig memb).

Definition wish_NonMemb pk uid ver dig nonMemb : iProp Σ :=
  ∃ label,
  let enc := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc nonMemb.(ktcore.NonMemb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label ∗
  "#Hwish_nonMemb" ∷ merkle.wish_NonMemb label nonMemb.(ktcore.NonMemb.MerkleProof) dig.

End proof.
End ktcore.
