From New.generatedproof.github_com.sanjit_bhat.pav Require Import client.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc auditor cryptoffi hashchain ktcore merkle server.

From New.proof.github_com.sanjit_bhat.pav.client_proof Require Import
  evidence.

Module client.
Import evidence.client.

Module epoch.
Record t :=
  mk' {
    epoch: w64;
    dig: list w8;
    link: list w8;
    sig: list w8;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj d : iProp Σ :=
  ∃ sl_dig sl_link sl_sig,
  "Hstruct" ∷ ptr ↦{d} (client.epoch.mk obj.(epoch) sl_dig sl_link sl_sig) ∗
  "Hsl_dig" ∷ sl_dig ↦*{d} obj.(dig) ∗
  "Hsl_link" ∷ sl_link ↦*{d} obj.(link) ∗
  "Hsl_sig" ∷ sl_sig ↦*{d} obj.(sig).

End proof.
End epoch.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition wish_checkMemb pk uid ver dig memb : iProp Σ :=
  ∃ label mapVal,
  let enc_label := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  let enc_val := ktcore.CommitOpen.pure_enc memb.(ktcore.Memb.PkOpen) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc_label memb.(ktcore.Memb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc_label label ∗
  "#His_mapVal" ∷ cryptoffi.is_hash (Some enc_val) mapVal ∗
  "#Hwish_memb" ∷ merkle.wish_VerifyMemb label mapVal memb.(ktcore.Memb.MerkleProof) dig.

Lemma wp_checkMemb ptr_pk pk (uid ver : w64) sl_dig dig ptr_memb memb :
  {{{
    is_pkg_init client ∗
    "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_pk pk ∗
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
    "#Hown_memb" ∷ ktcore.Memb.own ptr_memb memb (□)
  }}}
  @! client.checkMemb #ptr_pk #uid #ver #sl_dig #ptr_memb
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkMemb pk uid ver dig memb
      | false =>
        "#Hwish_checkMemb" ∷ wish_checkMemb pk uid ver dig memb
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_memb".
  wp_auto.
  wp_apply ktcore.wp_CheckMapLabel as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamed "Hgenie".
  iPersist "Hsl_label".
  wp_apply ktcore.wp_GetMapVal as "* @".
  { iFrame "#". }
  iPersist "Hsl_MapVal".
  wp_apply merkle.wp_VerifyMemb as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". iApply "Hgenie".
    iDestruct (cryptoffi.is_vrf_out_det with "His_out His_vrf_out") as %->.
    iDestruct (cryptoffi.is_hash_det with "His_MapVal His_mapVal") as %->.
    iFrame "#". }
  iNamedSuffix "Hgenie" "_merk".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  2: { iApply "HΦ". iIntros "@".
    iDestruct (cryptoffi.is_vrf_out_det with "His_out His_vrf_out") as %->.
    iDestruct (cryptoffi.is_hash_det with "His_MapVal His_mapVal") as %->.
    iDestruct (merkle.wish_VerifyMemb_det with "His_proof_merk Hwish_memb") as %->.
    done. }
  iApply "HΦ".
  iFrame "#".
Qed.

Definition wish_checkHist pk uid (prefixLen : w64) dig hist : iProp Σ :=
  ([∗ list] ver ↦ memb ∈ hist,
    wish_checkMemb pk uid (uint.Z prefixLen + ver) dig memb).

Lemma wp_checkHist ptr_pk pk (uid prefixLen : w64) sl_dig dig sl_hist sl0_hist hist :
  {{{
    is_pkg_init client ∗
    "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_pk pk ∗
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
    "#Hsl_hist" ∷ sl_hist ↦*□ sl0_hist ∗
    "#Hown_hist" ∷ ([∗ list] ptr;memb ∈ sl0_hist;hist,
      ktcore.Memb.own ptr memb (□))
  }}}
  @! client.checkHist #ptr_pk #uid #prefixLen #sl_dig #sl_hist
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkHist pk uid prefixLen dig hist
      | false =>
        "#Hwish_checkHist" ∷ wish_checkHist pk uid prefixLen dig hist
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iDestruct (own_slice_len with "Hsl_hist") as %[? _].
  iDestruct (big_sepL2_length with "Hown_hist") as %?.
  iAssert (
    ∃ (i : w64) (x0 : loc) (x1 : w64),
    "err" ∷ err_ptr ↦ into_val_typed_bool.(default_val bool) ∗
    "hist" ∷ hist_ptr ↦ sl_hist ∗
    "dig" ∷ dig_ptr ↦ sl_dig ∗
    "prefixLen" ∷ prefixLen_ptr ↦ prefixLen ∗
    "uid" ∷ uid_ptr ↦ uid ∗
    "vrfPk" ∷ vrfPk_ptr ↦ ptr_pk ∗
    "memb" ∷ memb_ptr ↦ x0 ∗
    "ver" ∷ ver_ptr ↦ x1 ∗
    "i" ∷ i_ptr ↦ i ∗

    "%Hlt_i" ∷ ⌜0%Z ≤ sint.Z i ≤ length hist⌝ ∗
    "#Hwish" ∷ ([∗ list] ver ↦ memb ∈ take (sint.nat i) hist,
      wish_checkMemb pk uid (uint.Z prefixLen + ver) dig memb)
  )%I with "[-HΦ]" as "IH".
  { iFrame. iSplit; [word|naive_solver]. }
  wp_for "IH".
  wp_if_destruct.
  { list_elem sl0_hist (sint.Z i) as ptr_memb.
    list_elem hist (sint.Z i) as memb.
    iDestruct (big_sepL2_lookup with "Hown_hist") as "#Hown_memb"; [done..|].
    wp_pure; [word|].
    wp_apply wp_load_slice_elem as "_"; [word|..].
    { by iFrame "#". }
    wp_apply wp_checkMemb as "* @".
    { iFrame "#". }
    wp_if_destruct; wp_for_post.
    { iApply "HΦ". iIntros "#H0". iApply "Hgenie".
      iDestruct (big_sepL_lookup with "H0") as "#H1"; [done|].
      iExactEq "H1". repeat f_equal. word. }
    iNamed "Hgenie".
    iFrame "∗#".
    iSplit; [word|].
    replace (sint.nat (word.add _ _)) with (S (sint.nat i)) by word.
    erewrite take_S_r; [|done].
    rewrite big_sepL_snoc.
    iFrame "#".
    iExactEq "Hwish_checkMemb".
    repeat f_equal. len. }

  iApply "HΦ".
  assert (i = length hist) as -> by word.
  rewrite take_ge; [|word].
  iFrame "#".
Qed.

Definition wish_checkNonMemb pk uid ver dig nonMemb : iProp Σ :=
  ∃ label,
  let enc := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc nonMemb.(ktcore.NonMemb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label ∗
  "#Hwish_nonMemb" ∷ merkle.wish_VerifyNonMemb label nonMemb.(ktcore.NonMemb.MerkleProof) dig.

Lemma wp_checkNonMemb ptr_pk pk (uid ver : w64) sl_dig dig ptr_nonMemb nonMemb :
  {{{
    is_pkg_init client ∗
    "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_pk pk ∗
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
    "#Hown_nonMemb" ∷ ktcore.NonMemb.own ptr_nonMemb nonMemb (□)
  }}}
  @! client.checkNonMemb #ptr_pk #uid #ver #sl_dig #ptr_nonMemb
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkNonMemb pk uid ver dig nonMemb
      | false =>
        "#Hwish_checkNonMemb" ∷ wish_checkNonMemb pk uid ver dig nonMemb
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_nonMemb".
  wp_auto.
  wp_apply ktcore.wp_CheckMapLabel as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamed "Hgenie".
  iPersist "Hsl_label".
  wp_apply merkle.wp_VerifyNonMemb as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". iApply "Hgenie".
    iDestruct (cryptoffi.is_vrf_out_det with "His_out His_vrf_out") as %->.
    iFrame "#". }
  iNamedSuffix "Hgenie" "_merk".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  2: { iApply "HΦ". iIntros "@".
    iDestruct (cryptoffi.is_vrf_out_det with "His_out His_vrf_out") as %->.
    iDestruct (merkle.wish_VerifyNonMemb_det with "His_proof_merk Hwish_nonMemb") as %->.
    done. }
  iApply "HΦ".
  iFrame "#".
Qed.

Definition wish_checkAudit servPk adtrPk ep reply : iProp Σ :=
  "#Hwish_adtr_vrfSig" ∷ ktcore.wish_VerifyVrfSig adtrPk
    reply.(auditor.GetReply.VrfPk) reply.(auditor.GetReply.AdtrVrfSig) ∗
  "#Hwish_serv_vrfSig" ∷ ktcore.wish_VerifyVrfSig servPk
    reply.(auditor.GetReply.VrfPk) reply.(auditor.GetReply.ServVrfSig) ∗
  "#Hwish_adtr_linkSig" ∷ ktcore.wish_VerifyLinkSig adtrPk ep
    reply.(auditor.GetReply.Link) reply.(auditor.GetReply.AdtrLinkSig) ∗
  "#Hwish_serv_linkSig" ∷ ktcore.wish_VerifyLinkSig servPk ep
    reply.(auditor.GetReply.Link) reply.(auditor.GetReply.ServLinkSig).

Lemma wp_checkAudit sl_servPk servPk sl_adtrPk adtrPk (ep : w64) ptr_reply reply :
  {{{
    is_pkg_init client ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hsl_adtrPk" ∷ sl_adtrPk ↦*□ adtrPk ∗
    "#Hown_reply" ∷ auditor.GetReply.own ptr_reply reply (□)
  }}}
  @! client.checkAudit #sl_servPk #sl_adtrPk #ep #ptr_reply
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkAudit servPk adtrPk ep reply
      | false =>
        "#Hwish_checkAudit" ∷ wish_checkAudit servPk adtrPk ep reply
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_reply".
  wp_auto.
  wp_apply ktcore.wp_VerifyVrfSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "_adtr_vrf".
  wp_apply ktcore.wp_VerifyVrfSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "_serv_vrf".
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "_adtr_link".
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". by iApply "Hgenie". }
  iNamedSuffix "Hgenie" "_serv_link".
  iApply "HΦ".
  iFrame "#".
Qed.

(*
Definition wish_getNextEp sigPk last_ep chainProof sig next_ep next_vals : iProp Σ :=
  "%Hwish_chain" ∷ ⌜hashchain.wish_Verify chainProof next_vals⌝ ∗
  "%Heq_ep" ∷ ⌜uint.Z last_ep.(epoch.epoch) + length next_vals = uint.Z next_ep.(epoch.epoch)⌝ ∗
  "%Heq_dig" ∷ ⌜last next_vals = Some next_ep.(epoch.dig)⌝ ∗
  "#His_link_sig" ∷ ktcore.wish_VerifyLinkSig sigPk next_ep.(epoch.epoch) next_ep.(epoch.link) next_ep.(epoch.sig).

Lemma wp_getNextEp ptr_last last sl_sigPk sigPk sl_chainProof chainProof sl_sig sig
    old_vals cut len :
  {{{
    is_pkg_init client ∗
    "#Hown_last" ∷ epoch.own ptr_last last (□) ∗
    "#Hsl_sigPk" ∷ sl_sigPk ↦*□ sigPk ∗
    "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig ∗
    "#His_chain_last" ∷ hashchain.is_chain old_vals cut last.(epoch.link) len
  }}}
  @! client.getNextEp #ptr_last #sl_sigPk #sl_chainProof #sl_sig
  {{{
    ptr_next (err : bool), RET (#ptr_next, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ next next_vals, wish_getNextEp sigPk last chainProof sig next next_vals
      | false =>
        ∃ next next_vals,
        "#Hown_next" ∷ epoch.own ptr_next next (□) ∗
        "#Hwish_getNextEp" ∷ wish_getNextEp sigPk last chainProof sig next next_vals ∗
        "#His_chain_next" ∷ hashchain.is_chain (old_vals ++ next_vals) cut next.(epoch.link)
          (len + length next_vals)
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_last".
  wp_auto.
  wp_apply (hashchain.wp_Verify with "[$Hsl_link $Hsl_chainProof $His_chain_last]").
  iIntros "*". iNamed 1.
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *.
    iApply "Hgenie". naive_solver. }
  iNamed "Hgenie".
  wp_if_destruct.
  { iApply "HΦ".
    iPersist "Hstruct Hsl_dig Hsl_link Hsl_sig".
    iFrame "#".
    iExists last, [].
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    apply last_None in Heq_dig' as ?.
    apply (f_equal length) in H.
    autorewrite with len in *.
    iFrame "#".
    iPureIntro. split; [word|done]. }
  iNamedSuffix "Hgenie" "chain".
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { iApply "HΦ". iNamedSuffix 1 "'". simpl in *.
    iApply "Hgenie".
    iIntros (?? (?&?&?&?)).
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    word. }
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. iApply "Hgenie".
    iIntros (?? (?&?&?&?)).
    opose proof (hashchain.wish_Verify_det _ _ _ Hwish_chain Hwish_chain') as ->.
    iDestruct (hashchain.is_chain_det with "His_chain_chain His_chain_chain'") as %<-.
    iExactEq "His_link_sig'". repeat f_equal. word. }
  iNamed "Hgenie".
  wp_apply wp_alloc as "* Hstruct".
  iApply "HΦ".
  iPersist "Hstruct Hsl_newVal Hsl_newLink Hsl_sig".
  iFrame "#".
  iExists new_vals.
  iFrame "#".
  iPureIntro. split; [word|].
  destruct (last _) eqn:Heq; [done|].
  apply last_None in Heq.
  apply (f_equal length) in Heq.
  simpl in *. word.
Qed.
*)

End proof.
End client.
