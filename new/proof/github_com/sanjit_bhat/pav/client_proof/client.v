From New.generatedproof.github_com.sanjit_bhat.pav Require Import client.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import bytes.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc auditor cryptoffi hashchain ktcore merkle server sigpred.

From New.proof.github_com.sanjit_bhat.pav.client_proof Require Import
  evidence rpc.

Module client.
Import evidence.client rpc.client.

Module nextVer.
Record t :=
  mk' {
    ver: w64;
    pendingPk: option $ list w8;

    isGoodClis: bool;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition uid_inv γ : iProp Σ :=
  ∃ puts,
  "Hputs" ∷ mono_list_auth_own γ 1 puts.
Definition is_uid_inv γ : iProp Σ := inv nroot (uid_inv γ).

Definition own ptr obj : iProp Σ :=
  ∃ isPending sl_pendingPk,
  "Hstruct_nextVer" ∷ ptr ↦ (client.nextVer.mk obj.(ver) isPending sl_pendingPk) ∗
  "#HpendingPk" ∷
    match obj.(pendingPk) with
    | None =>
      "%HisPending" ∷ ⌜isPending = false⌝
    | Some pk =>
      "%HisPending" ∷ ⌜isPending = true⌝ ∗
      "#Hsl_pendingPk" ∷ sl_pendingPk ↦*□ pk
    end.

Definition align_serv_pend obj uid γ : iProp Σ :=
  ∃ uidγ,
  "%Hlook_uidγ" ∷ ⌜γ.(server.cfg.uidγ) !! uid = Some uidγ⌝ ∗
  "HgoodCli" ∷
    match obj.(isGoodClis) with
    | true =>
      ∃ puts,
      "Hputs" ∷ mono_list_auth_own uidγ 1 puts ∗
      "%Hbound" ∷ ⌜∀ ver' pk, (ver', pk) ∈ puts → uint.Z ver' ≤ uint.Z obj.(ver)⌝ ∗
      "%Heq_pend" ∷ ⌜∀ pk, (obj.(ver), pk) ∈ puts → obj.(pendingPk) = Some pk⌝
    | false =>
      "#Huid_inv" ∷ is_uid_inv uidγ
    end.

Definition align_serv_hist obj uid γ (lastEp : w64) : iProp Σ :=
  ∃ i (entry : list w8 * server.keys_ty),
  "#Hidx_hist" ∷ mono_list_idx_own γ.(server.cfg.histγ) i entry ∗
  "%Hlt_ep" ∷ ⌜i ≤ uint.nat lastEp⌝ ∗
  "%Hver_hist" ∷ ⌜uint.nat obj.(ver) ≤ length (entry.2 !!! uid)⌝.

End proof.
End nextVer.

Module serv.
Record t :=
  mk' {
    vrfSig: list w8;

    (* TODO: maybe unwrap servInfo into this record. *)
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
  "Halign_pend_pend" ∷ match obj.(serv).(serv.good) with None => True | Some γ =>
    nextVer.align_serv_pend obj.(pend) obj.(uid) γ end ∗
  "#Halign_pend_hist" ∷ match obj.(serv).(serv.good) with None => True | Some γ =>
    nextVer.align_serv_hist obj.(pend) obj.(uid) γ obj.(last).(epoch.epoch) end ∗
  "#Hown_last" ∷ epoch.own ptr_last obj.(last) obj.(serv).(serv.info) ∗
  "#Halign_last" ∷ match obj.(serv).(serv.good) with None => True | Some γ =>
    epoch.align_serv obj.(last) γ end ∗
  "#Hown_serv" ∷ serv.own ptr_serv obj.(serv).

End proof.
End Client.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Lemma wp_getNextEp ptr_prev prev info sl_sigPk sigPk sl_chainProof chainProof sl_sig sig :
  {{{
    is_pkg_init client ∗
    "#Hown_prev" ∷ epoch.own ptr_prev prev info ∗
    "#Hsl_sigPk" ∷ sl_sigPk ↦*□ sigPk ∗
    "%Heq_sigPk" ∷ ⌜sigPk = info.(servInfo.sig_pk)⌝ ∗
    "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
    "#Hsl_sig" ∷ sl_sig ↦*□ sig
  }}}
  @! client.getNextEp #ptr_prev #sl_sigPk #sl_chainProof #sl_sig
  {{{
    ptr_next (err : bool), RET (#ptr_next, #err);
    "Hgenie" ∷
      match err with
      | true => ¬ ∃ digs next, wish_getNextEp prev sigPk chainProof sig digs next
      | false =>
        ∃ digs next,
        "#Hwish_getNextEp" ∷ wish_getNextEp prev sigPk chainProof sig digs next ∗
        "#Hown_next" ∷ epoch.own ptr_next next info
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
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { iApply "HΦ". iIntros "@".
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain HnewDigs) as <-.
    word. }
  wp_apply ktcore.wp_VerifyLinkSig as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { iApply "HΦ". iIntros "@". iApply "Hgenie".
    opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chain HnewDigs) as <-.
    simplify_eq/=.
    iDestruct (hashchain.is_chain_det with "His_chain HnextLink") as %<-.
    iExactEq "HnextSig". repeat f_equal. word. }
  iNamed "Hgenie".
  iPersist "prev".
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ v,
    ∃ sl_nextDig nextDig,
    "->" ∷ ⌜v = execute_val⌝ ∗
    "nextDig" ∷ nextDig_ptr ↦ sl_nextDig ∗
    "%HnextDig" ∷ ⌜last (prev.(epoch.digs) ++ new_vals) = Some nextDig⌝ ∗
    "#Hsl_nextDig" ∷ sl_nextDig ↦*□ nextDig
    )%I
    with "[nextDig]"
  ) as "* @".
  { wp_if_destruct.
    - destruct new_vals; simpl in *; try done.
      list_simplifier.
      by iFrame "∗#%".
    - destruct new_vals using rev_ind; simpl in *; [word|]. clear IHnew_vals.
      rewrite (assoc _) !last_snoc /=.
      by iFrame "∗#". }
  rewrite -wp_fupd.
  wp_apply wp_alloc as "* Hptr_next".
  iPersist "Hptr_next".
  iModIntro.
  iApply "HΦ".

  (* TODO[word]: w/o explicitly providing w64,
  something unfolds w64 to Naive.wrap and Naive.unsigned,
  which fails word tactic. *)
  iExists _, (epoch.mk' (word.add prev.(epoch.epoch) extLen) _ _ _
    (prev.(epoch.digs) ++ new_vals) _).
  iFrame "Hptr_next #%". simpl in *.
  repeat iSplit; [done|word|..].
  - iExactEq "His_chain". rewrite /named. repeat f_equal. word.
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
      | true => ¬ auditor.wish_SignedLink servPk adtrPk ep link
      | false =>
        "#Hwish_SignedLink" ∷ auditor.wish_SignedLink servPk adtrPk ep link
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
      | true => ¬ auditor.wish_SignedVrf servPk adtrPk vrf
      | false =>
        "#Hwish_SignedVrf" ∷ auditor.wish_SignedVrf servPk adtrPk vrf
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
    "%Heq_pend" ∷
      ⌜match c.(Client.pend).(nextVer.pendingPk) with
      | None => True
      | Some pk' => pk = pk'
      end⌝
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
  simplify_eq/=.
  (* destruct last0. *)
  wp_auto. simpl.
  iPersist "c pk".
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ v,
    ∃ sl_pendingPk',
    "->" ∷ ⌜v = execute_val⌝ ∗
    "Hstruct_client" ∷ ptr_c ↦ {|
                                 client.Client.uid' := uid;
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
    - destruct pendingPk; iNamed "HpendingPk"; try done.
      simplify_eq/=.
      wp_apply bytes.wp_Equal as "_".
      { iFrame "#". }
      wp_apply std.wp_Assert.
      { by case_bool_decide. }
      by iFrame "∗#".
    - by iFrame "∗#". }

  destruct good; iNamed "Halign_pend_pend".
  2: {
    wp_apply (server.wp_CallPut _ None).
    { iFrame "#". }
    iApply "HΦ". by iFrame "∗ Hown_last #". }
  simpl in *. destruct isGoodClis; iNamed "HgoodCli".
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
    (* TODO: pin down isReg and sl_pk. *)
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
          (e.(epoch.digs) ++ new_digs) e.(epoch.cut)) c in
        "Hclient" ∷ Client.own ptr_c c' ∗
        "%Heq_ep" ∷ ⌜uint.Z ep = (uint.Z c.(Client.last).(epoch.epoch) + length new_digs)%Z⌝)
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hclient".
  iNamed "Hown_serv".
  iNamed "Hown_last".
  wp_auto.
  wp_apply wp_CallHistory as "* @".
  { iFrame "#".
    case_match; try done.
    iNamed "Halign_last".
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
  { by iFrame "#". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    iApply "Hgenie".
    rewrite Heq_sig_pk.
    iDestruct ("Hgood" with "Halign_last [//]") as "@".
    iFrame "#". }
  iNamed "Hgenie".
  iNamedSuffix "Hown_next" "_next".
  wp_auto.
  iDestruct "Hsl_hist" as (?) "[Hsl0_hist Hsl_hist]".
  iDestruct (own_slice_len with "Hsl0_hist") as %[? ?].
  iDestruct (big_sepL2_length with "Hsl_hist") as %?.
  wp_apply wp_checkHist as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    iApply "Hgenie".
    rewrite Heq_sig_pk Heq_vrf_pk.
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    iFrame "#". }
  iNamed "Hgenie".
  wp_apply wp_checkNonMemb as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    iApply "Hgenie".
    rewrite Heq_sig_pk Heq_vrf_pk.
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    apply Forall2_length in Heq_hist0.
    autorewrite with len in *.
    iExactEq "Hwish_bound0". repeat f_equal. word. }
  iNamed "Hgenie".
  iPersist "hist boundVer".
  wp_bind (If _ _ _).
  wp_apply (wp_wand _ _ _
    (λ v,
    ∃ isReg sl_pk,
    "->" ∷ ⌜v = execute_val⌝ ∗
    "isReg" ∷ isReg_ptr ↦ isReg ∗
    "pk" ∷ pk_ptr ↦ sl_pk ∗
    "#Hlast_hist" ∷
      match last hist with
      | None => "%HisReg" ∷ ⌜isReg = false⌝
      | Some x =>
        "%HisReg" ∷ ⌜isReg = true⌝ ∗
        "#Hsl_pk" ∷ sl_pk ↦*□ x.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val)
      end
    )%I
    with "[isReg pk]"
  ) as "* @".
  { wp_if_destruct.
    - destruct (last hist) eqn:Hlast.
      { apply last_Some in Hlast as [? Hlast].
        apply (f_equal length) in Hlast.
        autorewrite with len in *. word. }
      by iFrame.
    - destruct (last hist) as [memb|] eqn:Hlast.
      2: { apply last_None in Hlast.
        apply (f_equal length) in Hlast.
        simpl in *. word. }
      remember (word.sub sl_hist.(slice.len_f) (W64 1)) as idx.
      rewrite last_lookup in Hlast.
      replace (pred _) with (sint.nat idx) in Hlast by word.
      list_elem ptr0 (sint.nat idx) as ptr_memb.
      iDestruct (big_sepL2_lookup with "Hsl_hist") as "H"; [done..|].
      iNamedSuffix "H" "0".
      iNamedSuffix "Hown_PkOpen0" "1".

      wp_pure; [word|].
      wp_apply wp_load_slice_elem as "_"; [word|..].
      { by iFrame "#". }
      by iFrame "∗#". }

  iApply "HΦ".
  iSplit. { iPureIntro. apply ktcore.blame_none. }
  case_decide; try done.
  iPoseProof "Hwish_getNextEp" as "@".
  simplify_eq/=.
  iFrame "∗ Hstruct_epoch_next #%". simpl in *.
  case_match; try done.
  rewrite Heq_sig_pk Heq_vrf_pk.
  iDestruct ("Hgood" with "Halign_last [//]") as "H".
  iNamedSuffix "H" "0".
  iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
  iNamed "Halign_pend_hist".
  Opaque mono_list_idx_own.
  iFrame "#%". word.
Qed.

Lemma wp_Client_SelfMon ptr_c c :
  {{{
    is_pkg_init client ∗
    "Hclient" ∷ Client.own ptr_c c
  }}}
  ptr_c @ (ptrT.id client.Client.id) @ "SelfMon" #()
  {{{
    (ep : w64) (isChanged : bool) err,
    RET (#ep, #isChanged, #(ktcore.blame_to_u64 err));
    "%Hblame" ∷ ⌜ktcore.BlameSpec err
      ({[
        ktcore.BlameServFull:=option_bool c.(Client.serv).(serv.good);
        ktcore.BlameClients:=c.(Client.pend).(nextVer.isGoodClis)
      ]})⌝ ∗
    "Herr" ∷
      (if decide (err ≠ ∅)
      then "Hclient" ∷ Client.own ptr_c c
      else
        ∃ ver pendingPk new_digs dig link sig,
        let lastPendVer := c.(Client.pend).(nextVer.ver) in
        let lastPendPk := c.(Client.pend).(nextVer.pendingPk) in
        let lastEp := c.(Client.last).(epoch.epoch) in
        let c' :=
          set Client.pend (λ x, set nextVer.ver (λ _, ver)
            (set nextVer.pendingPk (λ _, pendingPk) x))
          (set Client.last (λ x, epoch.mk' ep dig link sig
            (x.(epoch.digs) ++ new_digs) x.(epoch.cut)) c) in
        "Hclient" ∷ Client.own ptr_c c' ∗
        "%Hpend" ∷
          ⌜match lastPendPk with
          | None => isChanged = false ∧ ver = lastPendVer ∧ pendingPk = lastPendPk
          | Some pk =>
            (isChanged = false ∧ ver = lastPendVer ∧ pendingPk = lastPendPk) ∨
            (isChanged = true ∧ uint.Z ver = (uint.Z lastPendVer + 1)%Z ∧
              pendingPk = None)
          end⌝ ∗
        "%Heq_ep" ∷ ⌜uint.Z ep = (uint.Z lastEp + length new_digs)%Z⌝)
  }}}.
Proof.
  wp_start as "@".
  iNamed "Hclient".
  destruct c.
  iNamed "Hown_pend".
  destruct pend.
  iNamed "Hown_last".
  destruct last0.
  iNamed "Hown_serv".
  destruct serv.
  destruct info.
  simplify_eq/=.
  wp_auto.
  wp_apply wp_CallHistory as "* @".
  { iFrame "#".
    iModIntro.
    case_match; try done.
    iNamed "Halign_last". simplify_eq/=.
    list_elem hist (uint.nat epoch) as e.
    iDestruct (mono_list_idx_own_get with "His_hist") as "Hidx_hist0"; [done|].
    iNamed "Halign_pend_hist". simplify_eq/=.
    iMod (server.hist_pks_prefix uid with "His_rpc Hidx_hist Hidx_hist0")
      as %?%prefix_length; [word|].
    iClear "Hidx_hist His_hist".
    iFrame "#". word. }
  case_bool_decide as Heq_err; wp_auto;
    rewrite ktcore.rw_Blame0 in Heq_err; subst.
  2: {
    iApply "HΦ".
    iSplit. {
      iPureIntro.
      eapply ktcore.blame_add_interp; [done|].
      apply map_singleton_subseteq_l.
      by simpl_map. }
    case_decide; try done.
    iFrame "∗#%". }
  case_decide; try done.
  iNamed "Herr".
  (* TODO: change spec to have objs come as first args. *)
  wp_apply (wp_getNextEp _ (epoch.mk' _ _ _ _ _ _) (servInfo.mk _ vrf_pk)) as "* @".
  { by iFrame "Hstruct_epoch #". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    simplify_eq/=.
    iApply "Hgenie".
    iDestruct ("Hgood" with "Halign_last [//]") as "@".
    iFrame "#". }
  iNamed "Hgenie".
  iNamedSuffix "Hown_next" "_next".
  iDestruct "Hsl_hist" as (?) "[Hsl0_hist Hsl_hist]".
  iDestruct (own_slice_len with "Hsl0_hist") as %[? ?].
  iDestruct (big_sepL2_length with "Hsl_hist") as %?.
  wp_auto.
  wp_apply std.wp_SumNoOverflow.
  wp_if_destruct.
  2: { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    simplify_eq/=.
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    apply Forall2_length in Heq_hist0.
    autorewrite with len in *.
    word. }
  wp_apply wp_checkHist as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    simplify_eq/=.
    iApply "Hgenie".
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    iFrame "#". }
  iNamed "Hgenie".
  wp_apply wp_checkNonMemb as "* @".
  { iFrame "#". }
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit. 2: { case_decide; try done. by iFrame "∗#%". }
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    simplify_eq/=.
    iApply "Hgenie".
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    apply Forall2_length in Heq_hist0.
    autorewrite with len in *.
    iExactEq "Hwish_bound0". repeat f_equal. word. }
  iNamed "Hgenie".

  wp_if_destruct.
  2: {
    destruct pendingPk; iNamed "HpendingPk"; try done.
    wp_if_destruct.
    2: { rewrite ktcore.rw_BlameServClients.
      iApply "HΦ".
      iSplit. 2: { case_decide; [|set_solver]. by iFrame "∗#%". }
      iApply ktcore.blame_two.
      iSplit; [done|].
      iIntros ([? ->]).
      case_match; try done.
      simplify_eq/=.
      iNamed "Halign_pend_pend".
      iNamed "HgoodCli".
      iDestruct ("Hgood" with "Halign_last [//]") as "H".
      iNamedSuffix "H" "0".

      apply Forall2_length in Heq_hist0.
      autorewrite with len in *.
      remember (lastKeys !!! _) as pks.
      list_elem pks (uint.nat ver) as pk.
      case_decide.
      { apply lookup_lt_Some in Hpk_lookup. word. }
      iNamed "Hpend_gs0".
      simplify_eq/=.
      iDestruct (big_sepL_lookup with "Hidx_pks") as "[% #Hidx_bad]"; [done|].
      iDestruct (mono_list_auth_idx_lookup with "Hputs Hidx_bad") as %Hlook_bad.
      iPureIntro.
      apply list_elem_of_lookup_2 in Hlook_bad.
      ereplace (W64 (uint.nat ?[w])) with (?w) in Hlook_bad by word.
      by apply Heq_pend in Hlook_bad. }

    iApply "HΦ".
    iSplit. { iPureIntro. apply ktcore.blame_none. }
    case_decide; try done.
    iPoseProof "Hwish_getNextEp" as "@".
    simplify_eq/=.
    iFrame "∗ Hstruct_epoch_next #%". simpl in *.
    iSplit; [|done].
    iSplit; [done|].
    case_match; try done.
    simplify_eq/=.
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    iNamed "Halign_pend_hist".
    Opaque mono_list_idx_own.
    iFrame "#%". word. }
  destruct pendingPk; iNamed "HpendingPk"; try done.

  wp_if_destruct.
  { rewrite ktcore.rw_BlameServClients.
    iApply "HΦ".
    iSplit. 2: { case_decide; [|set_solver]. by iFrame "∗#%". }
    iApply ktcore.blame_two.
    iSplit; [done|].
    iIntros ([? ->]).
    case_match; try done.
    simplify_eq/=.
    iNamed "Halign_pend_pend".
    iNamed "HgoodCli".
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".

    apply Forall2_length in Heq_hist0.
    autorewrite with len in *.
    remember (lastKeys !!! _) as pks.
    list_elem pks (S $ uint.nat ver) as pk.
    case_decide.
    { apply lookup_lt_Some in Hpk_lookup. word. }
    iNamed "Hpend_gs0".
    simplify_eq/=.
    iDestruct (big_sepL_lookup with "Hidx_pks") as "[% #Hidx_bad]"; [done|].
    iDestruct (mono_list_auth_idx_lookup with "Hputs Hidx_bad") as %Hlook_bad.
    iPureIntro.
    apply list_elem_of_lookup_2 in Hlook_bad.
    eapply Hbound in Hlook_bad.
    word. }

  wp_if_destruct.
  { iApply "HΦ".
    iSplit. { iPureIntro. apply ktcore.blame_none. }
    case_decide; try done.
    iPoseProof "Hwish_getNextEp" as "@".
    simplify_eq/=.
    iFrame "∗ Hstruct_epoch_next #%". simpl in *.
    iSplit; [|naive_solver].
    iSplit; [done|].
    case_match; try done.
    simplify_eq/=.
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".
    iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
    iNamed "Halign_pend_hist".
    Opaque mono_list_idx_own.
    iFrame "#%". word. }

  list_elem ptr0 0 as ptr_memb.
  list_elem hist 0 as memb.
  iDestruct (big_sepL2_lookup with "Hsl_hist") as "H"; [done..|].
  iNamedSuffix "H" "0".
  iNamedSuffix "Hown_PkOpen0" "1".
  wp_pure; [word|].
  wp_apply wp_load_slice_elem as "_"; [word|..].
  { by iFrame "#". }
  wp_apply bytes.wp_Equal as "_".
  { iFrame "#". }
  wp_if_destruct.
  2: { rewrite ktcore.rw_BlameServClients.
    iApply "HΦ".
    iSplit. 2: { case_decide; [|set_solver]. by iFrame "∗#%". }
    iApply ktcore.blame_two.
    iSplit; [done|].
    iIntros ([? ->]).
    case_match; try done.
    simplify_eq/=.
    iNamed "Halign_pend_pend".
    iNamed "HgoodCli".
    iDestruct ("Hgood" with "Halign_last [//]") as "H".
    iNamedSuffix "H" "0".

    opose proof (Forall2_lookup_r _ _ _ _ _ Heq_hist0 ltac:(done)) as (?&Hlook_pks&?).
    simplify_eq/=.
    rewrite lookup_drop in Hlook_pks.
    apply Forall2_length in Heq_hist0 as ?.
    autorewrite with len in *.
    case_decide; [word|].
    iNamed "Hpend_gs0".
    simplify_eq/=.
    iDestruct (big_sepL_lookup with "Hidx_pks") as "[% #Hidx_bad]"; [done|].
    iDestruct (mono_list_auth_idx_lookup with "Hputs Hidx_bad") as %Hlook_bad.
    iPureIntro.
    apply list_elem_of_lookup_2 in Hlook_bad.
    ereplace (W64 (uint.nat ?[w] + Z.to_nat 0)%nat) with (?w) in Hlook_bad by word.
    apply Heq_pend in Hlook_bad.
    simplify_eq/=. }

  iApply "HΦ".
  iSplit. { iPureIntro. apply ktcore.blame_none. }
  case_decide; try done.
  iPoseProof "Hwish_getNextEp" as "@".
  simplify_eq/=.
  (* TODO[word]: w64 getting unfolded to Naive.wrap. *)
  iExists (word.add ver sl_hist.(slice.len_f)).
  iFrame "Hstruct_client Hstruct_nextVer Hstruct_epoch_next".
  simpl in *. iFrame "#%".
  iExists _.
  iSplit. 2: { iPureIntro. right. repeat split. word. }
  iSplit; [done|].
  case_match; try done.
  simplify_eq/=.
  iDestruct ("Hgood" with "Halign_last [//]") as "H".
  iNamedSuffix "H" "0".
  iDestruct (wish_getNextEp_det with "Hwish_getNextEp Hwish_getNextEp0") as %[-> ->].
  iFrame "#".
  iSplit.
  - iNamed "Halign_pend_pend". iFrame "%". simpl in *.
    destruct isGoodClis; [|done].
    iNamed "HgoodCli".
    iFrame.
    iPureIntro. split.
    + intros ?? Ht. apply Hbound in Ht. word.
    + intros ? Ht. apply Hbound in Ht. word.
  - rewrite last_lookup in Hlast_servHist0.
    iDestruct (mono_list_idx_own_get with "Hlb_servHist0") as "$"; [done|].
    simpl in *.
    apply Forall2_length in Heq_hist0.
    autorewrite with len in *.
    iSplit; word.
Qed.

End proof.
End client.
