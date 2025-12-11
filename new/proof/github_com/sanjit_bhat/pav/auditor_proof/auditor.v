From New.generatedproof.github_com.sanjit_bhat.pav Require Import auditor.

From New.proof Require Import bytes sync.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc cryptoffi hashchain ktcore merkle server sigpred.

From New.proof.github_com.sanjit_bhat.pav.auditor_proof Require Import
  base serde.

(* TODO: bad New.proof.sync exports.
https://github.com/mit-pdos/perennial/issues/470 *)
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module auditor.
Import base.auditor serde.auditor.

Module cfg.
Record t :=
  mk {
    serv_sig_pk: list w8;
    adtr_sig_pk: list w8;
    sigpredγ: sigpred.cfg.t;
  }.
End cfg.

Module history.
Record t :=
  mk' {
    link: list w8;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Definition own ptr obj ep γ : iProp Σ :=
  ∃ sl_link sl_servSig servSig sl_adtrSig adtrSig,
  "#Hstr_history" ∷ ptr ↦□ (auditor.history.mk sl_link sl_servSig sl_adtrSig) ∗
  "#Hsl_link" ∷ sl_link ↦*□ obj.(link) ∗
  "#Hsl_servSig" ∷ sl_servSig ↦*□ servSig ∗
  "#His_servSig" ∷ ktcore.wish_LinkSig γ.(cfg.serv_sig_pk) ep obj.(link) servSig ∗
  "#Hsl_adtrSig" ∷ sl_adtrSig ↦*□ adtrSig ∗
  "#His_adtrSig" ∷ ktcore.wish_LinkSig γ.(cfg.adtr_sig_pk) ep obj.(link) adtrSig.

End proof.
End history.

Module serv.
Record t :=
  mk' {
    vrfPk: list w8;

    good: option server.cfg.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj γ : iProp Σ :=
  ∃ ptr_cli sl_sigPk sl_vrfPk sl_servVrfSig servVrfSig sl_adtrVrfSig adtrVrfSig,
  "#Hstr_serv" ∷ ptr ↦□ (auditor.serv.mk ptr_cli sl_sigPk sl_vrfPk sl_servVrfSig sl_adtrVrfSig) ∗
  "#His_rpc" ∷ server.is_Server_rpc ptr_cli obj.(good) ∗
  "#Hsl_sigPk" ∷ sl_sigPk ↦*□ γ.(cfg.serv_sig_pk) ∗
  "#Hsl_vrfPk" ∷ sl_vrfPk ↦*□ obj.(vrfPk) ∗
  "#Hsl_servVrfSig" ∷ sl_servVrfSig ↦*□ servVrfSig ∗
  "#His_servVrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.serv_sig_pk) obj.(vrfPk) servVrfSig ∗
  "#Hsl_adtrVrfSig" ∷ sl_adtrVrfSig ↦*□ adtrVrfSig ∗
  "#His_adtrVrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.adtr_sig_pk) obj.(vrfPk) adtrVrfSig ∗

  "#His_sigPk" ∷ match obj.(good) with None => True | Some servγ =>
    cryptoffi.is_sig_pk γ.(cfg.serv_sig_pk)
      (sigpred.pred servγ.(server.cfg.sigpredγ)) end ∗
  (* trusted. *)
  "%Heq_sig_pk" ∷ ⌜match obj.(good) with None => True | Some servγ =>
    γ.(cfg.serv_sig_pk) = servγ.(server.cfg.sig_pk) end⌝ ∗
  (* from signed vrf_pk. *)
  "%Heq_vrf_pk" ∷ ⌜match obj.(good) with None => True | Some servγ =>
    obj.(vrfPk) = servγ.(server.cfg.vrf_pk) end⌝.

End proof.
End serv.

Module Auditor.
Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

(* length hist ≤ length digs ≤ total # eps. *)
Definition own ptr γ (q : Qp) : iProp Σ :=
  ∃ (digs : list $ list w8) (cut : option $ list w8) serv
    ptr_sk sl_lastDig lastDig (startEp : w64) sl_hist (sl0_hist : list loc)
    ptr_serv (lastEp : w64),
  (* separate struct fields bc "mu" contained in lock perm. *)
  "#Hfld_sk" ∷ ptr ↦s[auditor.Auditor::"sk"]□ ptr_sk ∗
  "Hfld_lastDig" ∷ ptr ↦s[auditor.Auditor::"lastDig"]{# q} sl_lastDig ∗
  "#Hfld_startEp" ∷ ptr ↦s[auditor.Auditor::"startEp"]□ startEp ∗
  "Hfld_hist" ∷ ptr ↦s[auditor.Auditor::"hist"]{# q} sl_hist ∗
  "#Hfld_serv" ∷ ptr ↦s[auditor.Auditor::"serv"]□ ptr_serv ∗

  "#Hown_sk" ∷ cryptoffi.own_sig_sk ptr_sk γ.(cfg.adtr_sig_pk)
    (sigpred.pred γ.(cfg.sigpredγ)) ∗
  "Hsl_lastDig" ∷ sl_lastDig ↦*{#q} lastDig ∗
  "%Heq_lastDig" ∷ ⌜last digs = Some lastDig⌝ ∗
  "Hsl_hist" ∷ sl_hist ↦*{#q} sl0_hist ∗
  "Hcap_hist" ∷ own_slice_cap loc sl_hist (DfracOwn q) ∗
  "#Hown_serv" ∷ serv.own ptr_serv serv γ ∗

  (* allows proving Get spec. *)
  "#Hhist" ∷ ([∗ list] idx ↦ ptr_hist ∈ sl0_hist,
    ∃ link,
    let num_digs := (length digs - length sl0_hist + idx + 1)%nat in
    "#His_link" ∷ hashchain.is_chain (take num_digs digs) cut link num_digs ∗
    "#Hown_hist" ∷ history.own ptr_hist (history.mk' link) (uint.nat startEp + idx) γ) ∗
  "%Hlt_hist" ∷ ⌜length sl0_hist ≤ length digs⌝ ∗
  "%Hnoof_lastEp" ∷ ⌜uint.Z startEp + length sl0_hist - 1 = uint.Z lastEp⌝ ∗

  (* allows proving Update BlameSpec. *)
  "#Hgood" ∷ match serv.(serv.good) with None => True | Some servγ =>
    ∃ (hist : list (list w8 * server.keys_ty)),
    "#Hlb_hist" ∷ mono_list_lb_own servγ.(server.cfg.histγ) hist ∗
    "%Heq_digs" ∷ ⌜digs = hist.*1⌝ ∗
    "%Heq_cut" ∷ ⌜cut = None⌝ end.

Definition lock_perm ptr γ : iProp Σ :=
  ∃ ptr_mu,
  "#Hfld_mu" ∷ ptr ↦s[auditor.Auditor::"mu"]□ ptr_mu ∗
  "Hperm" ∷ own_RWMutex ptr_mu (own ptr γ).

End proof.
End Auditor.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition wish_CheckStartChain servPk chain (ep : w64) dig link : iProp Σ :=
  ∃ digs0 digs1 cut,
  "%Hlen_link_prev" ∷ ⌜Z.of_nat $ length chain.(server.StartChain.PrevLink) = cryptoffi.hash_len⌝ ∗
  "#His_chain_prev" ∷ hashchain.is_chain digs0 cut chain.(server.StartChain.PrevLink)
    (uint.nat chain.(server.StartChain.PrevEpochLen)) ∗
  "%Hwish_chain" ∷ ⌜hashchain.wish_Proof chain.(server.StartChain.ChainProof) digs1⌝ ∗
  "#His_chain_start" ∷ hashchain.is_chain (digs0 ++ digs1) cut link
    (uint.nat chain.(server.StartChain.PrevEpochLen) + length digs1) ∗
  "%Heq_ep" ∷ ⌜uint.Z chain.(server.StartChain.PrevEpochLen) + length digs1 - 1 = uint.Z ep⌝ ∗
  "%Heq_dig" ∷ ⌜last digs1 = Some dig⌝ ∗
  "#His_link_sig" ∷ ktcore.wish_LinkSig servPk ep link chain.(server.StartChain.LinkSig).

Lemma wish_CheckStartChain_det pk c e0 e1 d0 d1 l0 l1 :
  wish_CheckStartChain pk c e0 d0 l0 -∗
  wish_CheckStartChain pk c e1 d1 l1 -∗
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

Lemma wp_CheckStartChain sl_servPk servPk ptr_chain chain :
  {{{
    is_pkg_init auditor ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hown_chain" ∷ server.StartChain.own ptr_chain chain (□)
  }}}
  @! auditor.CheckStartChain #sl_servPk #ptr_chain
  {{{
    (ep : w64) sl_dig sl_link (err : bool),
    RET (#ep, #sl_dig, #sl_link, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ ep dig link, wish_CheckStartChain servPk chain ep dig link
      | false =>
        ∃ dig link,
        "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
        "#Hsl_link" ∷ sl_link ↦*□ link ∗
        "#Hwish_CheckStartChain" ∷ wish_CheckStartChain servPk chain ep dig link
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_chain". destruct chain. simpl.
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
  iDestruct (hashchain.is_chain_hash_len with "His_chain_prev") as %?.
  iApply "HΦ".
  iFrame "#%". simpl in *.
  iPureIntro. split; [word|].
  destruct (last _) eqn:Heq; [done|].
  apply last_None in Heq.
  apply (f_equal length) in Heq.
  simpl in *. word.
Qed.

Definition wish_CheckStartVrf servPk vrf : iProp Σ :=
  "#His_vrf_pk" ∷ cryptoffi.is_vrf_pk vrf.(server.StartVrf.VrfPk) ∗
  "#His_vrf_sig" ∷ ktcore.wish_VrfSig servPk vrf.(server.StartVrf.VrfPk)
    vrf.(server.StartVrf.VrfSig).

Lemma wp_CheckStartVrf sl_servPk servPk ptr_vrf vrf :
  {{{
    is_pkg_init auditor ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hown_vrf" ∷ server.StartVrf.own ptr_vrf vrf (□)
  }}}
  @! auditor.CheckStartVrf #sl_servPk #ptr_vrf
  {{{
    ptr_vrfPk (err : bool),
    RET (#ptr_vrfPk, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ wish_CheckStartVrf servPk vrf
      | false =>
        "#Hwish_CheckStartVrf" ∷ wish_CheckStartVrf servPk vrf ∗
        "#Hown_vrf_pk" ∷ cryptoffi.own_vrf_pk ptr_vrfPk vrf.(server.StartVrf.VrfPk)
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_vrf". destruct vrf. simpl.
  wp_auto.
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
  iApply "HΦ".
  iFrame "#%".
Qed.

Lemma wp_getNextDig sl_prevDig prevDig prevMap sl_updates updates :
  {{{
    is_pkg_init auditor ∗
    "#Hsl_prevDig" ∷ sl_prevDig ↦*□ prevDig ∗
    "#His_prevMap" ∷ merkle.is_map prevMap prevDig ∗
    "#Hown_updates" ∷ ktcore.UpdateProofSlice1D.own sl_updates updates (□)
  }}}
  @! auditor.getNextDig #sl_prevDig #sl_updates
  {{{
    sl_dig (err : bool), RET (#sl_dig, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ dig, ktcore.wish_ListUpdate prevDig updates dig
      | false =>
        ∃ dig map,
        "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
        "#His_map" ∷ merkle.is_map map dig ∗
        (* caller doesn't need to know map update elems. just subset. *)
        "%Hsub" ∷ ⌜prevMap ⊆ map⌝ ∗
        "#Hwish_ListUpdate" ∷ ktcore.wish_ListUpdate prevDig updates dig
      end
  }}}.
Proof.
  wp_start as "@". wp_auto.
  iPersist "updates".
  iDestruct "Hown_updates" as "(%sl0_updates&Hsl_updates&Hown_updates)".
  iDestruct (own_slice_len with "Hsl_updates") as %[? ?].
  iDestruct (big_sepL2_length with "Hown_updates") as %?.
  iAssert (
    ∃ (i : w64) sl_dig dig x map,
    let pref_updates := take (sint.nat i) updates in
    "i" ∷ i_ptr ↦ i ∗
    "%Hlt_i" ∷ ⌜0 ≤ sint.Z i ≤ length updates⌝ ∗
    "u" ∷ u_ptr ↦ x ∗
    "err" ∷ err_ptr ↦ false ∗
    "dig" ∷ dig_ptr ↦ sl_dig ∗
    "#Hsl_dig" ∷ sl_dig ↦*□ dig ∗
    "#His_map" ∷ merkle.is_map map dig ∗
    "%Hsub" ∷ ⌜prevMap ⊆ map⌝ ∗
    "#Hwish" ∷ ktcore.wish_ListUpdate prevDig pref_updates dig
  )%I with "[-HΦ]" as "IH".
  { iFrame "∗#".
    rewrite take_0.
    repeat iSplit; [word|word|done|].
    iExists [prevDig].
    repeat iSplit; try done. naive_solver. }

  wp_for "IH".
  wp_if_destruct.
  2: {
    replace (sint.nat i) with (length updates) in * by word.
    rewrite take_ge; [|lia].
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
  { wp_for_post. iApply "HΦ".
    iNamedSuffix 1 "0". iNamed "Hwish_aux0". iApply "Hgenie".
    iDestruct (big_sepL_lookup with "Hwish_upds") as "H"; [done|].
    iNamedSuffix "H" "0". iFrame "#". }
  iNamed "Hgenie".
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  2: { wp_for_post. iApply "HΦ".
    iNamedSuffix 1 "0". iNamed "Hwish".
    iDestruct (ktcore.wish_ListUpdate_aux_take (sint.nat i) with "Hwish_aux0") as "Hwish_aux1".
    iDestruct (ktcore.wish_ListUpdate_aux_det with "Hwish_aux Hwish_aux1") as %->.
    iNamed "Hwish_aux0".
    iDestruct (big_sepL_lookup with "Hwish_upds") as "@"; [done|].
    iDestruct (merkle.wish_Update_det with "His_proof Hwish_upd") as %[-> ->].
    rewrite last_lookup in Hlast.
    apply lookup_take_Some in Hlast as [Hlast _].
    replace (pred _) with (sint.nat i) in Hlast by len.
    by simplify_eq/=. }
  wp_for_post.
  iFrame "∗#".
  iSplit; [word|].
  iSplit.
  - iDestruct (merkle.is_map_inj with "His_map His_map_old") as %<-.
    iPureIntro.
    trans map; try done.
    by apply insert_subseteq.
  - replace (sint.nat (word.add _ _)) with (S $ sint.nat i) by word.
    erewrite take_S_r; [|done].
    iApply ktcore.wish_ListUpdate_grow; iFrame "#".
Qed.

Definition wish_SignedLink servPk adtrPk ep link : iProp Σ :=
  "#Hwish_adtr_sig" ∷ ktcore.wish_LinkSig adtrPk ep
    link.(SignedLink.Link) link.(SignedLink.AdtrSig) ∗
  "#Hwish_serv_sig" ∷ ktcore.wish_LinkSig servPk ep
    link.(SignedLink.Link) link.(SignedLink.ServSig).

Definition wish_SignedVrf servPk adtrPk vrf : iProp Σ :=
  "#Hwish_adtr_sig" ∷ ktcore.wish_VrfSig adtrPk
    vrf.(SignedVrf.VrfPk) vrf.(SignedVrf.AdtrSig) ∗
  "#Hwish_serv_sig" ∷ ktcore.wish_VrfSig servPk
    vrf.(SignedVrf.VrfPk) vrf.(SignedVrf.ServSig).

Lemma wp_Auditor_Get a γ epoch :
  {{{
    is_pkg_init auditor ∗
    "Hlock" ∷ Auditor.lock_perm a γ
  }}}
  a @ (ptrT.id auditor.Auditor.id) @ "Get" #epoch
  {{{
    ptr_link ptr_vrf err, RET (#ptr_link, #ptr_vrf, #err);
    "Hlock" ∷ Auditor.lock_perm a γ ∗
    (* client doesn't require anything of this err. *)
    "Herr" ∷ match err with true => True | false =>
      ∃ link vrf,
      "#Hown_link" ∷ SignedLink.own ptr_link link (□) ∗
      "#Hown_vrf" ∷ SignedVrf.own ptr_vrf vrf (□) ∗
      "#Hwish_link" ∷ wish_SignedLink γ.(cfg.serv_sig_pk) γ.(cfg.adtr_sig_pk) epoch link ∗
      "#Hwish_vrf" ∷ wish_SignedVrf γ.(cfg.serv_sig_pk) γ.(cfg.adtr_sig_pk) vrf end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hlock".
  wp_apply wp_with_defer as "* Hdefer".
  simpl. wp_auto.
  wp_apply (wp_RWMutex__RLock with "[$Hperm]") as "[Hlocked H]".
  iNamed "H". wp_auto.
  wp_if_destruct.
  { wp_apply (wp_RWMutex__RUnlock with "[-HΦ]") as "Hlock".
    { iFrame "∗∗#%". }
    iApply "HΦ". iFrame "∗#". }
  wp_if_destruct.
  { wp_apply (wp_RWMutex__RUnlock with "[-HΦ]") as "Hlock".
    { iFrame "∗∗#%". }
    iApply "HΦ". iFrame "∗#". }

  iDestruct (own_slice_len with "Hsl_hist") as %[? ?].
  wp_pure; [word|].
  list_elem sl0_hist (sint.nat (word.sub epoch startEp)) as ptr_epoch.
  iDestruct (big_sepL_lookup with "Hhist") as "@"; [done|].
  iNamed "Hown_hist".
  iNamed "Hown_serv".
  wp_apply (wp_load_slice_elem with "[$Hsl_hist]") as "Hsl_hist"; [word|done|].
  wp_apply wp_alloc as "* Hptr_link".
  wp_apply wp_alloc as "* Hptr_vrf".
  iPersist "Hptr_link Hptr_vrf".
  wp_apply (wp_RWMutex__RUnlock with "[-HΦ]") as "Hlock".
  { iFrame "∗∗ Hstr_serv #%". }
  iApply "HΦ". iFrame "Hfld_mu ∗".
  simpl in *.
  iExists (SignedLink.mk' _ _ _), (SignedVrf.mk' _ _ _).
  replace (W64 (uint.nat _ + sint.nat _)) with epoch by word.
  iFrame "#".
Qed.

End proof.
End auditor.
