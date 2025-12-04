From New.generatedproof.github_com.sanjit_bhat.pav Require Import client.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc auditor cryptoffi hashchain ktcore merkle server sigpred.

From New.proof.github_com.sanjit_bhat.pav.client_proof Require Import
  evidence.

Module client.
Import evidence.client.

(* client info about the server, regardless of the server trust.
these fields may be diff from the "global" [server.cfg.t]. *)
Module servInfo.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
  }.
End servInfo.

Module epoch.
Record t :=
  mk' {
    epoch: w64;
    dig: list w8;
    link: list w8;
    sig: list w8;

    digs: list $ list w8;
    cut: option $ list w8;
    serv: servInfo.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_dig sl_link sl_sig,
  "#Hstruct_epoch" ∷ ptr ↦□ (client.epoch.mk obj.(epoch) sl_dig sl_link sl_sig) ∗
  "#Hsl_dig" ∷ sl_dig ↦*□ obj.(dig) ∗
  "#Hsl_link" ∷ sl_link ↦*□ obj.(link) ∗
  "#Hsl_sig" ∷ sl_sig ↦*□ obj.(sig) ∗

  "%Hlast_dig" ∷ ⌜last obj.(digs) = Some obj.(dig)⌝ ∗
  "#His_chain" ∷ hashchain.is_chain obj.(digs) obj.(cut) obj.(link) (S $ uint.nat obj.(epoch)) ∗
  "#His_sig" ∷ ktcore.wish_LinkSig obj.(serv).(servInfo.sig_pk)
    obj.(epoch) obj.(link) obj.(sig).

(* separate [own] from [correct] to allow proving "pure" specs on [own]. *)
Definition correct obj γ : iProp Σ :=
  ∃ hist,
  "#His_hist" ∷ mono_list_lb_own γ.(server.cfg.histγ) hist ∗
  "%Heq_digs" ∷ ⌜obj.(digs) = hist.*1⌝ ∗
  "%Heq_cut" ∷ ⌜obj.(cut) = None⌝ ∗
  "%Heq_ep" ∷ ⌜length hist = S $ uint.nat obj.(epoch)⌝.

End proof.
End epoch.

Module nextVer.
Record t :=
  mk' {
    ver: w64;
    pendingPk: option $ list w8;

    uid: w64;
    servGood: option server.cfg.t;
    isGoodClis: bool;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition uid_inv γ : iProp Σ :=
  ∃ puts,
  "Hputs" ∷ mono_list_auth_own γ 1 puts.
Definition is_uid_inv γ := inv nroot (uid_inv γ).

Definition own ptr obj : iProp Σ :=
  ∃ isPending sl_pendingPk,
  "Hstruct_nextVer" ∷ ptr ↦ (client.nextVer.mk obj.(ver) isPending sl_pendingPk) ∗
  "#Hsl_pendingPk" ∷
    match obj.(pendingPk) with
    | None =>
      "%HisPending" ∷ ⌜isPending = false⌝
    | Some pk =>
      "%HisPending" ∷ ⌜isPending = true⌝ ∗
      "#Hsl_pendingPk" ∷ sl_pendingPk ↦*□ pk
    end ∗

  "Hown_uid" ∷ match obj.(servGood) with None => True | Some cfg =>
    ∃ uidγ,
    "%Hlook_uidγ" ∷ ⌜cfg.(server.cfg.uidγ) !! obj.(uid) = Some uidγ⌝ ∗
    "HgoodCli" ∷
      if obj.(isGoodClis)
      then
        ∃ puts,
        "Hputs" ∷ mono_list_auth_own uidγ 1 puts ∗
        "%Hbound" ∷ ⌜∀ ver' pk, (ver', pk) ∈ puts → uint.Z ver' ≤ uint.Z obj.(ver)⌝ ∗
        "%Heq_pend" ∷ ⌜∀ pk, (obj.(ver), pk) ∈ puts → obj.(pendingPk) = Some pk⌝
      else
        "#Huid_inv" ∷ is_uid_inv uidγ end.

End proof.
End nextVer.

Module serv.
Record t :=
  mk' {
    vrfSig: list w8;

    info: servInfo.t;
    good: option server.cfg.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ ptr_cli sl_sigPk ptr_vrfPk sl_vrfSig,
  "#Hstruct_serv" ∷ ptr ↦□ (client.serv.mk ptr_cli sl_sigPk ptr_vrfPk sl_vrfSig) ∗
  "#His_rpc" ∷ server.is_Server_rpc ptr_cli obj.(good) ∗
  "#Hsl_sigPk" ∷ sl_sigPk ↦*□ obj.(info).(servInfo.sig_pk) ∗
  "#Hown_vrfPk" ∷ cryptoffi.own_vrf_pk ptr_vrfPk obj.(info).(servInfo.vrf_pk) ∗
  "#Hsl_vrfSig" ∷ sl_vrfSig ↦*□ obj.(vrfSig) ∗
  "#His_vrfSig" ∷ ktcore.wish_VrfSig obj.(info).(servInfo.sig_pk)
    obj.(info).(servInfo.vrf_pk) obj.(vrfSig) ∗

  "#His_sigPk" ∷ match obj.(good) with None => True | Some cfg =>
    cryptoffi.is_sig_pk obj.(info).(servInfo.sig_pk)
      (sigpred.pred cfg.(server.cfg.sigpredγ)) end ∗
  (* trusted. *)
  "%Heq_sig_pk" ∷ ⌜match obj.(good) with None => True | Some cfg =>
    obj.(info).(servInfo.sig_pk) = cfg.(server.cfg.sig_pk) end⌝ ∗
  (* from signed vrf_pk. *)
  "%Heq_vrf_pk" ∷ ⌜match obj.(good) with None => True | Some cfg =>
    obj.(info).(servInfo.vrf_pk) = cfg.(server.cfg.vrf_pk) end⌝.

End proof.
End serv.

Module Client.
Record t :=
  mk' {
    uid: w64;
    pend: nextVer.t;
    last: epoch.t;
    serv: serv.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ ptr_pend ptr_last ptr_serv,
  "Hstruct_client" ∷ ptr ↦ (client.Client.mk obj.(uid) ptr_pend ptr_last ptr_serv) ∗
  "Hown_pend" ∷ nextVer.own ptr_pend obj.(pend) ∗
  "#Hown_last" ∷ epoch.own ptr_last obj.(last) ∗
  "#Hgood_last" ∷ match obj.(serv).(serv.good) with None => True | Some γ =>
    epoch.correct obj.(last) γ end ∗
  "#Hown_serv" ∷ serv.own ptr_serv obj.(serv) ∗

  "%Heq_serv" ∷ ⌜obj.(serv).(serv.info) = obj.(last).(epoch.serv)⌝ ∗
  "%Heq_servGood1" ∷ ⌜obj.(serv).(serv.good) = obj.(pend).(nextVer.servGood)⌝ ∗
  "%Heq_uid" ∷ ⌜obj.(uid) = obj.(pend).(nextVer.uid)⌝.

End proof.
End Client.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition wish_getNextEp prev sigPk chainProof sig next : iProp Σ :=
  ∃ new_vals,
  "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof new_vals⌝ ∗
  "#Hlen_vals" ∷
    (if decide (new_vals = [])
    then "%Heq_next" ∷ ⌜next = prev⌝
    else
      ∃ newEp newLink,
      "%HnewEp" ∷ ⌜uint.Z newEp = (uint.Z prev.(epoch.epoch) + length new_vals)%Z⌝ ∗
      "#His_new_chain" ∷ hashchain.is_chain (prev.(epoch.digs) ++ new_vals)
        prev.(epoch.cut) newLink (S $ uint.nat newEp) ∗
      "#Hwish_sig" ∷ ktcore.wish_LinkSig sigPk newEp newLink sig ∗
      "%Heq_next" ∷ ⌜next = epoch.mk' newEp (default [] (last new_vals))
        newLink sig (prev.(epoch.digs) ++ new_vals)
        prev.(epoch.cut) prev.(epoch.serv)⌝).

#[global] Instance wish_getNextEp_pers prev pk chain sig next :
  Persistent (wish_getNextEp prev pk chain sig next).
Proof.
  rewrite /wish_getNextEp.
  apply exist_persistent. intros.
  case_decide; apply _.
Qed.

Lemma wp_getNextEp ptr_prev prev sl_sigPk sigPk sl_chainProof chainProof sl_sig sig :
  {{{
    is_pkg_init client ∗
    "#Hown_prev" ∷ epoch.own ptr_prev prev ∗
    "#Hsl_sigPk" ∷ sl_sigPk ↦*□ sigPk ∗
    "%Heq_sigPk" ∷ ⌜sigPk = prev.(epoch.serv).(servInfo.sig_pk)⌝ ∗
    "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! client.getNextEp #ptr_prev #sl_sigPk #sl_chainProof #sl_sig
  {{{
    ptr_next (err : bool), RET (#ptr_next, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ next, wish_getNextEp prev sigPk chainProof sig next
      | false =>
        ∃ next,
        "#Hwish_getNextEp" ∷ wish_getNextEp prev sigPk chainProof sig next ∗
        "#Hown_next" ∷ epoch.own ptr_next next
      end
  }}}.
Proof.
  wp_start as "@".
  iNamedSuffix "Hown_prev" "_prev".
  wp_auto.
  wp_apply hashchain.wp_Verify as "* @".
  { iFrame "#". }
  iPersist "Hsl_newVal Hsl_newLink".
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". simpl in *. iApply "Hgenie". naive_solver. }
  iNamed "Hgenie".
  wp_if_destruct.
  { iApply "HΦ". iFrame "#%". case_decide; [done|]. by destruct new_vals. }
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { iApply "HΦ". iIntros "@".
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain Hwish_chainProof) as <-.
    case_decide as Heq.
    { apply (f_equal length) in Heq. simpl in *. word. }
    iNamed "Hlen_vals". word. }
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". iApply "Hgenie".
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain Hwish_chainProof) as <-.
    case_decide as Heq.
    { apply (f_equal length) in Heq. simpl in *. word. }
    iNamed "Hlen_vals".
    iDestruct (hashchain.is_chain_det with "His_chain His_new_chain") as %<-.
    iExactEq "Hwish_sig". repeat f_equal. word. }
  iNamed "Hgenie".
  rewrite -wp_fupd.
  wp_apply wp_alloc as "* Hptr_next".
  iPersist "Hptr_next".
  iModIntro.
  iApply "HΦ".
  (* TODO[word]: w/o explicitly providing w64,
  something unfolds w64 to Naive.wrap and Naive.unsigned,
  which fails word tactic. *)
  iExists (epoch.mk' (word.add prev.(epoch.epoch) extLen) _ _ _ _ _ _).
  iFrame "Hptr_next #%". simpl in *.
  case_decide as Heq.
  { apply (f_equal length) in Heq. simpl in *. word. }
  iFrame "#".
  repeat iSplit; try iPureIntro; try done.
  - word.
  - iExactEq "His_chain". rewrite /named. repeat f_equal. word.
  - destruct new_vals using rev_ind; [done|]. clear IHnew_vals.
    by rewrite (assoc _) !last_snoc.
  - iExactEq "His_chain". rewrite /named. repeat f_equal. word.
Qed.

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
      | true => ¬ ktcore.wish_Memb pk uid ver dig memb
      | false =>
        "#Hwish_Memb" ∷ ktcore.wish_Memb pk uid ver dig memb
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
    iDestruct (merkle.wish_Memb_det with "His_proof_merk Hwish_memb") as %->.
    done. }
  iApply "HΦ".
  iFrame "#".
Qed.

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
      | true => ¬ ktcore.wish_ListMemb pk uid prefixLen dig hist
      | false =>
        "#Hwish_ListMemb" ∷ ktcore.wish_ListMemb pk uid prefixLen dig hist
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
      ktcore.wish_Memb pk uid (uint.Z prefixLen + ver) dig memb)
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
    iExactEq "Hwish_Memb".
    repeat f_equal. len. }

  iApply "HΦ".
  assert (i = length hist) as -> by word.
  rewrite take_ge; [|word].
  iFrame "#".
Qed.

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
      | true => ¬ ktcore.wish_NonMemb pk uid ver dig nonMemb
      | false =>
        "#Hwish_NonMemb" ∷ ktcore.wish_NonMemb pk uid ver dig nonMemb
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
    iDestruct (merkle.wish_NonMemb_det with "His_proof_merk Hwish_nonMemb") as %->.
    done. }
  iApply "HΦ".
  iFrame "#".
Qed.

Definition wish_checkAuditLink servPk adtrPk ep link : iProp Σ :=
  "#Hwish_adtr_linkSig" ∷ ktcore.wish_LinkSig adtrPk ep
    link.(auditor.SignedLink.Link) link.(auditor.SignedLink.AdtrSig) ∗
  "#Hwish_serv_linkSig" ∷ ktcore.wish_LinkSig servPk ep
    link.(auditor.SignedLink.Link) link.(auditor.SignedLink.ServSig).

Lemma wp_checkAuditLink sl_servPk servPk sl_adtrPk adtrPk (ep : w64) ptr_link link :
  {{{
    is_pkg_init client ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hsl_adtrPk" ∷ sl_adtrPk ↦*□ adtrPk ∗
    "#Hown_link" ∷ auditor.SignedLink.own ptr_link link (□)
  }}}
  @! client.checkAuditLink #sl_servPk #sl_adtrPk #ep #ptr_link
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkAuditLink servPk adtrPk ep link
      | false =>
        "#Hwish_checkAuditLink" ∷ wish_checkAuditLink servPk adtrPk ep link
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_link".
  wp_auto.
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

Definition wish_checkAuditVrf servPk adtrPk vrf : iProp Σ :=
  "#Hwish_adtr_vrfSig" ∷ ktcore.wish_VrfSig adtrPk
    vrf.(auditor.SignedVrf.VrfPk) vrf.(auditor.SignedVrf.AdtrSig) ∗
  "#Hwish_serv_vrfSig" ∷ ktcore.wish_VrfSig servPk
    vrf.(auditor.SignedVrf.VrfPk) vrf.(auditor.SignedVrf.ServSig).

Lemma wp_checkAuditVrf sl_servPk servPk sl_adtrPk adtrPk ptr_vrf vrf :
  {{{
    is_pkg_init client ∗
    "#Hsl_servPk" ∷ sl_servPk ↦*□ servPk ∗
    "#Hsl_adtrPk" ∷ sl_adtrPk ↦*□ adtrPk ∗
    "#Hown_vrf" ∷ auditor.SignedVrf.own ptr_vrf vrf (□)
  }}}
  @! client.checkAuditVrf #sl_servPk #sl_adtrPk #ptr_vrf
  {{{
    (err : bool), RET #err;
    "Hgenie" ∷
      match err with
      | true => ¬ wish_checkAuditVrf servPk adtrPk vrf
      | false =>
        "#Hwish_checkAuditVrf" ∷ wish_checkAuditVrf servPk adtrPk vrf
      end
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hown_vrf".
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
  iApply "HΦ".
  iFrame "#".
Qed.

Lemma wp_Client_Put ptr_c c sl_pk pk :
  {{{
    is_pkg_init client ∗
    "Hclient" ∷ Client.own ptr_c c ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "%Heq_pend" ∷ ⌜match c.(Client.pend).(nextVer.pendingPk) with None => True
      | Some pk' => pk = pk' end⌝
  }}}
  ptr_c @ (ptrT.id client.Client.id) @ "Put" #sl_pk
  {{{
    RET #();
    let c' := set Client.pend (λ p, set nextVer.pendingPk (λ _, Some pk) p) c in
    "Hclient" ∷ Client.own ptr_c c'
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hclient".
  destruct c.
  iNamed "Hown_pend".
  destruct pend.
  iNamed "Hown_serv".
  destruct serv.
  destruct last0.
  simplify_eq/=.
  wp_auto. simpl.
  iPersist "c pk".
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ v,
    ∃ sl_pendingPk',
    "->" ∷ ⌜v = execute_val⌝ ∗
    "Hstruct_client" ∷ ptr_c ↦ {|
                                 client.Client.uid' := uid0;
                                 client.Client.pend' := ptr_pend;
                                 client.Client.last' := ptr_last;
                                 client.Client.serv' := ptr_serv
                               |} ∗
    "Hstruct_nextVer" ∷ ptr_pend ↦ {|
                                     client.nextVer.ver' := ver;
                                     client.nextVer.isPending' := true;
                                     client.nextVer.pendingPk' := sl_pendingPk'
                                   |} ∗
    "#Hsl_pendingPk'" ∷ sl_pendingPk' ↦*□ pk
    )%I
    with "[Hstruct_client Hstruct_nextVer]"
  ) as "* @".
  { wp_if_destruct.
    - destruct pendingPk; iNamed "Hsl_pendingPk"; try done.
      simplify_eq/=.
      wp_apply bytes.wp_Equal as "_".
      { iFrame "#". }
      wp_apply std.wp_Assert.
      { by case_bool_decide. }
      by iFrame "∗#".
    - by iFrame "∗#". }

  destruct servGood; iNamed "Hown_uid".
  2: {
    wp_apply (server.wp_CallPut _ None).
    { iFrame "#". }
    iApply "HΦ". by iFrame "∗ Hown_last #". }
  destruct isGoodClis; iNamed "HgoodCli".
  + iMod (mono_list_auth_own_update_app [(ver, pk)] with "Hputs") as "[Hputs #Hlb]".
    iDestruct (mono_list_idx_own_get (length puts) with "Hlb") as "#Hidx".
    { by rewrite lookup_snoc. }
    wp_apply (server.wp_CallPut _ (Some _)).
    { iFrame "#%". }
    iApply "HΦ".
    iFrame "∗ Hown_last #%". simpl in *.
    iPureIntro. repeat split; try done.
    * intros. decompose_list_elem_of; [naive_solver|].
      by simplify_eq/=.
    * intros. decompose_list_elem_of; [naive_solver|].
      by simplify_eq/=.
  + iApply fupd_wp.
    iInv "Huid_inv" as ">@" "Hclose".
    iMod (mono_list_auth_own_update_app [(ver, pk)] with "Hputs") as "[Hputs #Hlb]".
    iMod ("Hclose" with "[Hputs]") as "_"; [iFrame|].
    iModIntro.
    iDestruct (mono_list_idx_own_get (length puts) with "Hlb") as "#Hidx".
    { by rewrite lookup_snoc. }
    wp_apply (server.wp_CallPut _ (Some _)).
    { iFrame "#%". }
    iApply "HΦ".
    by iFrame "∗ Hown_last #%".
Qed.

Lemma wp_Client_Get ptr_c c (uid : w64) :
  {{{
    is_pkg_init client ∗
    "Hclient" ∷ Client.own ptr_c c
  }}}
  ptr_c @ (ptrT.id client.Client.id) @ "Get" #uid
  {{{
    (ep : w64) (isReg : bool) (sl_pk : slice.t) err,
    RET (#ep, #isReg, #sl_pk, #(ktcore.blame_to_u64 err));
    "%Hblame" ∷ ⌜ktcore.BlameSpec err
      {[ktcore.BlameServFull:=option_bool c.(Client.serv).(serv.good)]}⌝ ∗
    "Herr" ∷
      (if decide (err ≠ ∅)
      then "Hclient" ∷ Client.own ptr_c c
      else
        (* guarantee mono digs and ep match digs. *)
        ∃ new_digs dig link sig,
        let c' := set Client.last (λ e, epoch.mk' ep dig link sig
          (e.(epoch.digs) ++ new_digs) e.(epoch.cut) e.(epoch.serv)) c in
        "Hclient" ∷ Client.own ptr_c c' ∗
        "%Heq_ep" ∷ ⌜uint.Z ep = (uint.Z c.(Client.last).(epoch.epoch) + length new_digs)%Z⌝)
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hclient".
  iNamed "Hown_serv".
  iNamed "Hown_last".
  wp_auto.
  wp_apply server.wp_CallHistory as "* @".
  { iFrame "#".
    case_match; try done.
    iNamed "Hgood_last".
    list_elem hist (uint.nat c.(Client.last).(epoch.epoch)) as e.
    iDestruct (mono_list_idx_own_get with "His_hist") as "$"; [done|].
    word. }
  case_bool_decide as Heq_err; wp_auto;
    rewrite ktcore.rw_Blame0 in Heq_err; subst.
  2: {
    iApply "HΦ".
    iSplit; [done|].
    case_decide; try done.
    iFrame "∗#%". }
  case_decide; try done.
  iNamed "Herr".
  wp_apply wp_getNextEp as "* @".
  { iFrame "#". iPureIntro. split; [done|]. by rewrite Heq_serv. }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    iNamed "Hgood".
    iNamed "Hgood_last".
    iApply "Hgenie".

    iFrame "%".
    case_decide as Hlen_vals; [naive_solver|].
    iDestruct (mono_list_lb_valid with "His_hist Hlb_servHist") as %[[newHist ->]|Hpref].
    2: {
      apply prefix_length in Hpref.
      rewrite -skipn_all_iff in Hlen_vals.
      autorewrite with len in *. word. }
    rewrite {}Heq_digs {}Heq_cut.
    rewrite fmap_app drop_app_length'; [|len].

    iExists _, (W64 (uint.Z c.(Client.last).(epoch.epoch) + length newHist)), _.
    autorewrite with len in *.
    iSplit; [word|].
    iSplit. { iExactEq "His_lastLink". rewrite /named. repeat f_equal. word. }
    iSplit. { iExactEq "Hwish_linkSig". rewrite /named. repeat f_equal; [done|word]. }
    done. }
Admitted.

End proof.
End client.
