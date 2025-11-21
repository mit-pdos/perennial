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
  "%Hwish_chain" ∷ ⌜hashchain.wish_Proof reply.(server.StartReply.ChainProof) digs1⌝ ∗
  "#His_chain_start" ∷ hashchain.is_chain (digs0 ++ digs1) cut link
    (uint.nat reply.(server.StartReply.PrevEpochLen) + length digs1) ∗
  "%Heq_ep" ∷ ⌜uint.Z reply.(server.StartReply.PrevEpochLen) + length digs1 - 1 = uint.Z ep⌝ ∗
  "%Heq_dig" ∷ ⌜last digs1 = Some dig⌝ ∗
  "#His_link_sig" ∷ ktcore.wish_LinkSig servPk ep link reply.(server.StartReply.LinkSig) ∗

  (* vrf. *)
  "#His_vrf_pk" ∷ cryptoffi.is_vrf_pk reply.(server.StartReply.VrfPk) ∗
  "#His_vrf_sig" ∷ ktcore.wish_VrfSig servPk reply.(server.StartReply.VrfPk)
    reply.(server.StartReply.VrfSig).

Lemma wish_CheckStart_det pk r e0 e1 d0 d1 l0 l1 :
  wish_CheckStart pk r e0 d0 l0 -∗
  wish_CheckStart pk r e1 d1 l1 -∗
  ⌜e0 = e1 ∧ d0 = d1 ∧ l0 = l1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (hashchain.is_chain_inj with "His_chain_prev0 His_chain_prev1") as %[-> ->].
  opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain0 Hwish_chain1) as ->.
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
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain Hwish_chain') as ->.
    apply last_Some in Heq_dig' as [? Heq].
    apply (f_equal length) in Heq.
    autorewrite with len in *.
    word. }
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { iApply "HΦ". iNamedSuffix 1 "'". simpl in *.
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain Hwish_chain') as ->.
    word. }
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iNamedSuffix 1 "'". simpl in *. iApply "Hgenie".
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain Hwish_chain') as ->.
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

Definition wish_getNextDig_aux prevDig updates digs : iProp Σ :=
  "%Hlen" ∷ ⌜length digs = S (length updates)⌝ ∗
  "%Hhead" ∷ ⌜head digs = Some prevDig⌝ ∗
  "#Hwish_updates" ∷ ([∗ list] i ↦ upd ∈ updates,
    ∃ dig0 dig1,
    "%Hlook0" ∷ ⌜digs !! i = Some dig0⌝ ∗
    "%Hlook1" ∷ ⌜digs !! (S i) = Some dig1⌝ ∗
    "#Hwish" ∷ merkle.wish_Update upd.(ktcore.UpdateProof.MapLabel)
      upd.(ktcore.UpdateProof.MapVal) upd.(ktcore.UpdateProof.NonMembProof)
      dig0 dig1).

Lemma wish_getNextDig_aux_det prevDig updates digs0 digs1 :
  wish_getNextDig_aux prevDig updates digs0 -∗
  wish_getNextDig_aux prevDig updates digs1 -∗
  ⌜digs0 = digs1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iInduction updates as [] using rev_ind forall (digs0 digs1 Hlen0 Hlen1 Hhead0 Hhead1).
  { destruct digs0, digs1; try done.
    destruct digs0, digs1; try done.
    by simplify_eq/=. }
  destruct digs0 using rev_ind; try done. clear IHdigs0.
  destruct digs1 using rev_ind; try done. clear IHdigs1.
  autorewrite with len in *.
  iDestruct (big_sepL_snoc with "Hwish_updates0") as "{Hwish_updates0} [Hwish0 H0]".
  iDestruct (big_sepL_snoc with "Hwish_updates1") as "{Hwish_updates1} [Hwish1 H1]".
  iDestruct ("IHupdates" $! digs0 digs1 with "[][][][][][]") as %->.
  all: iClear "IHupdates".
  1-4: iPureIntro.
  { lia. }
  { lia. }
  { destruct digs0; try done. simpl in *. lia. }
  { destruct digs1; try done. simpl in *. lia. }
  { iModIntro. iApply (big_sepL_impl with "Hwish0"). iModIntro.
    iIntros (?? Hlook) "@".
    apply lookup_lt_Some in Hlook.
    rewrite !lookup_app_l in Hlook0, Hlook1; [|lia..].
    iFrame "#%". }
  { iModIntro. iApply (big_sepL_impl with "Hwish1"). iModIntro.
    iIntros (?? Hlook) "@".
    apply lookup_lt_Some in Hlook.
    rewrite !lookup_app_l in Hlook0, Hlook1; [|lia..].
    iFrame "#%". }
  iClear "Hwish0 Hwish1".
  iNamedSuffix "H0" "0".
  iNamedSuffix "H1" "1".
  iDestruct (merkle.wish_Update_det with "Hwish0 Hwish1") as %[-> ->].
  rewrite !lookup_app_r in Hlook10, Hlook11; [|lia..].
  apply list_lookup_singleton_Some in Hlook10 as [_ ->].
  apply list_lookup_singleton_Some in Hlook11 as [_ ->].
  done.
Qed.

Definition wish_getNextDig prevDig updates dig : iProp Σ :=
  ∃ digs,
  "#Hwish_aux" ∷ wish_getNextDig_aux prevDig updates digs ∗
  "%Hlast" ∷ ⌜last digs = Some dig⌝.

Lemma wish_getNextDig_det prevDig updates dig0 dig1 :
  wish_getNextDig prevDig updates dig0 -∗
  wish_getNextDig prevDig updates dig1 -∗
  ⌜dig0 = dig1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  iDestruct (wish_getNextDig_aux_det with "Hwish_aux0 Hwish_aux1") as %->.
  rewrite Hlast0 in Hlast1.
  by simplify_eq/=.
Qed.

Lemma wp_getNextDig sl_prevDig prevDig sl_updates sl0_updates updates mPrev :
  {{{
    is_pkg_init auditor ∗
    "#Hsl_prevDig" ∷ sl_prevDig ↦*□ prevDig ∗
    "#Hsl_updates" ∷ sl_updates ↦*□ sl0_updates ∗
    "#Hown_updates" ∷ ([∗ list] ptr;upd ∈ sl0_updates;updates,
      ktcore.UpdateProof.own ptr upd (□)) ∗
    "#His_map_prev" ∷ merkle.is_map mPrev prevDig
  }}}
  @! auditor.getNextDig #sl_prevDig #sl_updates
  {{{
    sl_dig dig (err : bool), RET (#sl_dig, #err);
    let updatesL := (λ x,
      (x.(ktcore.UpdateProof.MapLabel), x.(ktcore.UpdateProof.MapLabel)))
      <$> updates in
    let updatesM := list_to_map updatesL in
    let mNext := updatesM ∪ mPrev in
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ dig, wish_getNextDig prevDig updates dig
      | false =>
        "#Hwish_getNextDig" ∷ wish_getNextDig prevDig updates dig ∗
        "#His_map_next" ∷ merkle.is_map mNext dig ∗
        "%Hmono" ∷ ⌜mPrev ⊆ mNext⌝
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iPersist "updates".
  iDestruct (own_slice_len with "Hsl_updates") as %[? _].
  iDestruct (big_sepL2_length with "Hown_updates") as %?.
  iAssert (
    ∃ (i : w64) sl_dig dig digs ptr_u,
    let updatesSub := take (sint.nat i) updates in
    let updatesL := (λ x,
      (x.(ktcore.UpdateProof.MapLabel), x.(ktcore.UpdateProof.MapLabel)))
      <$> updatesSub in
    let updatesM := list_to_map updatesL in
    let mNext := updatesM ∪ mPrev in
    "i" ∷ i_ptr ↦ i ∗
    "%Hlt_i" ∷ ⌜0 ≤ sint.Z i ≤ length updates⌝ ∗
    "u" ∷ u_ptr ↦ ptr_u ∗
    "err" ∷ err_ptr ↦ false ∗
    "dig" ∷ dig_ptr ↦ sl_dig ∗
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗

    "#Hwish_aux" ∷ wish_getNextDig_aux prevDig updatesSub digs ∗
    "%Hlast" ∷ ⌜last digs = Some dig⌝ ∗
    "#His_map_next" ∷ merkle.is_map mNext dig ∗
    "%Hmono" ∷ ⌜mPrev ⊆ mNext⌝
  )%I with "[-HΦ]" as "IH".
  { iFrame "∗#".
    rewrite take_0 /= (left_id _).
    iFrame "#". iExists [prevDig].
    repeat iSplit; [word|word|done|done|naive_solver|done|done]. }

  wp_for "IH".
  wp_if_destruct.
  2: {
    replace (sint.nat i) with (length updates) in * by word.
    rewrite take_ge in Hmono |-*; [|lia].
    iApply "HΦ". iFrame "#%". }

  list_elem sl0_updates (sint.Z i) as ptr_upd.
  list_elem updates (sint.Z i) as upd.
  iDestruct (big_sepL2_lookup with "Hown_updates") as "#Hown_upd"; [done..|].
  iNamed "Hown_upd".
  wp_pure; [word|].
  wp_apply wp_load_slice_elem as "_"; [word|..].
  { by iFrame "#". }
  wp_apply merkle.wp_VerifyUpdate as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { wp_for_post. iApply "HΦ". iFrame "#".
    iNamedSuffix 1 "0". iNamed "Hwish_aux0". iApply "Hgenie".
    iDestruct (big_sepL_lookup with "Hwish_updates") as "@"; [done|].
    iFrame "#". }
  iNamed "Hgenie".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  2: { wp_for_post. iApply "HΦ". iFrame "#".
    iNamedSuffix 1 "0".
    admit. }
Admitted.
(*
  wp_for_post.
  iFrame.
  iPureIntro. split; [word|].
  replace (uint.nat (word.add _ _)) with (S (uint.nat i)) by word.
  iExists (digs ++ [newHash]).
  repeat iSplit.
  - iPureIntro. len.
  - by rewrite head_app.
  - iPureIntro. rewrite last_snoc. done.
  - erewrite take_S_r; [|done].
    rewrite big_sepL_app.
    iFrame "#".
    iApply big_sepL_singleton.
    iExists oldHash, newHash.
    repeat iSplit.
    + iPureIntro. by rewrite lookup_app_l; [|word].
    + iPureIntro. rewrite lookup_app_r; [|word].
      replace (S (uint.nat i) - length digs) with 0%nat by word.
      done.
    + iExactEq "His_proof". repeat f_equal.
      by rewrite -Hlast.
Qed.
*)

End proof.
End auditor.
