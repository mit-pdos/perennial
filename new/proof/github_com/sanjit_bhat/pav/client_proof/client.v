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

    serv: servInfo.t;
    servGood: option server.cfg.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_dig sl_link sl_sig digs cut,
  "#Hstruct" ∷ ptr ↦□ (client.epoch.mk obj.(epoch) sl_dig sl_link sl_sig) ∗
  "#Hsl_dig" ∷ sl_dig ↦*□ obj.(dig) ∗
  "#Hsl_link" ∷ sl_link ↦*□ obj.(link) ∗
  "#Hsl_sig" ∷ sl_sig ↦*□ obj.(sig) ∗

  "#Hlast_dig" ∷ ⌜last digs = Some obj.(dig)⌝ ∗
  "#His_chain" ∷ hashchain.is_chain digs cut obj.(link) (S $ uint.nat obj.(epoch)) ∗
  "#His_sig" ∷ ktcore.wish_LinkSig obj.(serv).(servInfo.sig_pk)
    obj.(epoch) obj.(link) obj.(sig) ∗

  "#Hserv_good" ∷ match obj.(servGood) with None => True | Some c =>
    ∃ hist,
    "#His_hist" ∷ mono_list_lb_own c.(server.cfg.histγ) hist ∗
    "%His_digs" ∷ ⌜hist.*1 = digs⌝ ∗
    "%Hcut" ∷ ⌜cut = None⌝
    end.

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

Definition own ptr obj : iProp Σ :=
  ∃ isPending sl_pendingPk,
  "Hstruct" ∷ ptr ↦ (client.nextVer.mk obj.(ver) isPending sl_pendingPk) ∗
  "#Hsl_pendingPk" ∷
    match obj.(pendingPk) with
    | None =>
      "%HisPending" ∷ ⌜isPending = false⌝
    | Some pk =>
      "%HisPending" ∷ ⌜isPending = true⌝ ∗
      "#Hsl_pendingPk" ∷ sl_pendingPk ↦*□ pk
    end ∗

  "Hown_uid" ∷
    match obj.(isGoodClis), obj.(servGood) with
    | true, Some cfg =>
      ∃ uidγ puts,
      "%Hlook_uidγ" ∷ ⌜cfg.(server.cfg.uidγ) !! obj.(uid) = Some uidγ⌝ ∗
      "Hputs" ∷ mono_list_auth_own uidγ 1 puts ∗

      "%Hbound" ∷ ⌜∀ ver' pk, (ver', pk) ∈ puts → uint.Z ver' ≤ uint.Z obj.(ver)⌝ ∗
      "%Hpending" ∷ ⌜∀ pk, (obj.(ver), pk) ∈ puts → obj.(pendingPk) = Some pk⌝
    | _, _ => True
    end.

End proof.
End nextVer.

Module serv.
Record t :=
  mk' {
    cli: loc;
    vrfSig: list w8;

    info: servInfo.t;
    good: option server.cfg.t;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj : iProp Σ :=
  ∃ sl_sigPk ptr_vrfPk sl_vrfSig,
  "#Hstruct" ∷ ptr ↦□ (client.serv.mk obj.(cli) sl_sigPk ptr_vrfPk sl_vrfSig) ∗
  "#Hsl_sigPk" ∷ sl_sigPk ↦*□ obj.(info).(servInfo.sig_pk) ∗
  "#Hown_vrfPk" ∷ cryptoffi.own_vrf_pk ptr_vrfPk obj.(info).(servInfo.vrf_pk) ∗
  "#Hsl_vrfSig" ∷ sl_vrfSig ↦*□ obj.(vrfSig) ∗
  "#His_vrfSig" ∷ ktcore.wish_VrfSig obj.(info).(servInfo.sig_pk)
    obj.(info).(servInfo.vrf_pk) obj.(vrfSig) ∗

  "#His_sigPk" ∷ match obj.(good) with None => True | Some cfg =>
    cryptoffi.is_sig_pk obj.(info).(servInfo.sig_pk)
      (sigpred.pred cfg.(server.cfg.sigpredγ))
    end.

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
  "Hstruct" ∷ ptr ↦ (client.Client.mk obj.(uid) ptr_pend ptr_last ptr_serv) ∗
  "Hown_pend" ∷ nextVer.own ptr_pend obj.(pend) ∗
  "#Hown_last" ∷ epoch.own ptr_last obj.(last) ∗
  "#Hown_serv" ∷ serv.own ptr_serv obj.(serv) ∗

  "%Heq_serv" ∷ ⌜obj.(serv).(serv.info) = obj.(last).(epoch.serv)⌝ ∗
  "%Heq_servGood0" ∷ ⌜obj.(serv).(serv.good) = obj.(last).(epoch.servGood)⌝ ∗
  "%Heq_servGood1" ∷ ⌜obj.(serv).(serv.good) = obj.(pend).(nextVer.servGood)⌝ ∗
  "%Heq_uid" ∷ ⌜obj.(uid) = obj.(pend).(nextVer.uid)⌝.

End proof.
End Client.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

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

End proof.
End client.
