From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import advrpc auditor core classes cryptoffi evidence merkle rpc serde server.
From Perennial.program_proof Require Import std_proof.
From Perennial.Helpers Require Import Map.

Module Client.
Record t :=
  mk {
    γ: gname;
    uid: uid_ty;
    next_ver: ver_ty;
    next_epoch: epoch_ty;
    serv_γ: gname;
    serv_sig_pk: list w8;
    serv_vrf_pk: loc;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; next_ver; next_epoch; serv_γ; serv_sig_pk; serv_vrf_pk>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition map_inv (m : cli_map_ty) (dig : list w8) : iProp Σ :=
  ([∗ map] k ↦ val ∈ m,
    ∃ label,
    "#His_label" ∷ is_vrf k.1 k.2 label ∗
    "#Hhas_mproof" ∷ has_merkp label
      ((λ x, MapValPre.encodesF (MapValPre.mk x.1 x.2)) <$> val) dig).

Definition inv γ : iProp Σ :=
  ∃ ms,
  "Hown_epochs" ∷ mono_list_auth_own γ (1/2)
    ((λ (x : option _), (λ y, y.1) <$> x) <$> ms) ∗
  "Hown_maps" ∷ ([∗ list] x ∈ ms,
    match x with None => True | Some (m_γ, _, m) =>
    ghost_map_auth m_γ 1 m end) ∗
  "#His_maps" ∷ ([∗ list] x ∈ ms,
    match x with None => True | Some (_, dig, m) => map_inv m dig end).

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ ms ptr_sd sd_ptrs sd ptr_serv_cli serv_cli sl_serv_sig_pk,
  (* seenDigs. *)
  "Hown_sd_map" ∷ own_map ptr_sd (DfracOwn 1) sd_ptrs ∗
  "#Hptr_sd" ∷ ptr ↦[Client :: "seenDigs"]□ #ptr_sd ∗
  "#Hown_sd" ∷ ([∗ map] l;v ∈ sd_ptrs;sd, SigDig.own l v) ∗
  "#His_sd" ∷ ([∗ map] x ∈ sd, is_SigDig x obj.(serv_sig_pk)) ∗
  (* GS. *)
  "#Hinv" ∷ inv nroot (inv obj.(γ)) ∗
  "Hown_epochs" ∷ mono_list_auth_own obj.(γ) (1/2)
    ((λ (x : option _), (λ y, y.1) <$> x) <$> ms) ∗
  "Hown_maps" ∷ ([∗ list] x ∈ ms,
    match x with None => True | Some (m_γ, _, m) =>
    ghost_map_auth m_γ (1/2) m end) ∗
  "%Hagree_sd" ∷ ([∗ list] ep ↦ x ∈ ms,
    match x with None => True | Some (_, dig, _) =>
    ∃ sig,
    "%Hlook_sd" ∷ ⌜ sd !! (W64 ep) = Some (SigDig.mk (W64 ep) dig sig) ⌝ end) ∗
  (* uid, next_ver, next_epoch. *)
  "#Hptr_uid" ∷ ptr ↦[Client :: "uid"]□ #obj.(uid) ∗
  "Hptr_nextVer" ∷ ptr ↦[Client :: "nextVer"] #obj.(next_ver) ∗
  "Hptr_nextEpoch" ∷ ptr ↦[Client :: "nextEpoch"] #obj.(next_epoch) ∗
  "%Heq_next_ep" ∷ ⌜ length ms = uint.nat obj.(next_epoch) ⌝ ∗
  "%Hlast_some" ∷ ⌜ ∀ m, last ms = Some m → is_Some m ⌝ ∗
  (* server info. *)
  "Hown_servCli" ∷ advrpc.Client.own ptr_serv_cli serv_cli ∗
  "#Hptr_servCli" ∷ ptr ↦[Client :: "servCli"]□ #ptr_serv_cli ∗
  "#Hptr_servSigPk" ∷ ptr ↦[Client :: "servSigPk"]□ (slice_val sl_serv_sig_pk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded obj.(serv_sig_pk) ∗
  "#Hptr_servVrfPk" ∷ ptr ↦[Client :: "servVrfPk"]□ #obj.(serv_vrf_pk).
(*
currently, mlist has option gname.
change it so that it grabs the first two things.
*)
End defs.
End Client.

(* TODO: rm Module. *)
Module clientErr.
Record t :=
  mk {
    evid: option Evid.t;
    err: bool;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) (pk : list w8) : iProp Σ :=
  ∃ (ptr_evid : loc),
  "Hptr_evid" ∷ ptr ↦[clientErr :: "evid"] #ptr_evid ∗
  "Hptr_err" ∷ ptr ↦[clientErr :: "err"] #obj.(err) ∗
  match obj.(evid) with
  | Some e =>
    "Hown_evid" ∷ Evid.own ptr_evid e ∗
    "#His_evid" ∷ is_Evid e pk
  | None => True
  end.
End defs.
End clientErr.

Section specs.
Context `{!heapGS Σ, !pavG Σ}.

Definition is_my_key cli_γ uid ver ep pk : iProp Σ :=
  ∃ m_γ dig comm,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (m_γ, dig)) ∗
  "#Hcomm" ∷ is_comm pk comm ∗
  "#Hin_map_lat" ∷ (uid, ver) ↪[m_γ]□ (Some (ep, comm)) ∗
  "#Hnin_map_next" ∷ (uid, word.add (W64 1) ver) ↪[m_γ]□ None.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    (ep : w64) ptr_err err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Herr" ∷ clientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    if negb err.(clientErr.err) then
      let new_c := set Client.next_ver (word.add (W64 1))
        (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_key" ∷ is_my_key c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep pk ∗
      "%Hnoof_ver" ∷ ⌜ uint.Z (word.add c.(Client.next_ver) (W64 1)) = (uint.Z c.(Client.next_ver) + 1)%Z ⌝ ∗
      "%Hnoof_eq" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) ≤ uint.Z ep ⌝
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_my_bound cli_γ uid ver (ep : w64) : iProp Σ :=
  ∃ m_γ dig,
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (m_γ, dig)) ∗
  "#Hnin_map_next" ∷ (uid, ver) ↪[m_γ]□ None.

Lemma wp_Client__SelfMon ptr_c c :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    (ep : w64) ptr_err err, RET (#ep, #ptr_err);
    "Herr" ∷ clientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    if negb err.(clientErr.err) then
      let new_c := (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_bound" ∷ is_my_bound c.(Client.γ) c.(Client.uid) c.(Client.next_ver) ep ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

Definition is_other_key cli_γ uid (ep : w64) (lat : lat_val_ty) : iProp Σ :=
  ∃ (vals : list opaque_map_val_ty) m_γ dig,
  "#Hpk_comm_reln" ∷ pk_comm_reln lat (last vals) ∗
  "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (m_γ, dig)) ∗
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ vals, (uid, W64 ver) ↪[m_γ]□ Some val) ∗
  "#Hbound" ∷ (uid, W64 $ length vals) ↪[m_γ]□ None.

Lemma wp_Client__Get ptr_c c uid :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    (is_reg : bool) sl_pk pk (ep : w64) ep' ptr_err err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Herr" ∷ clientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    if negb err.(clientErr.err) then
      let new_c := (set Client.next_epoch (λ _, word.add ep (W64 1)) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝ ∗
      "Hsl_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
      "#His_key" ∷ is_other_key c.(Client.γ) uid ep
        (if is_reg then Some (ep', pk) else None)
    else
      "Hown_cli" ∷ Client.own ptr_c c
  }}}.
Proof. Admitted.

(* is_audit says we've audited up *to* (not including) bound. *)
Definition is_audit (cli_γ adtr_γ : gname) (bound : w64) : iProp Σ :=
  ∃ ms,
  "#Hadtr_maps" ∷ mono_list_lb_own adtr_γ ms ∗
  "%Hlen_maps" ∷ ⌜ length ms = uint.nat bound ⌝ ∗
  "%Hinv_adtr" ∷ ⌜ adtr_inv ms ⌝ ∗
  "#Hmap_transf" ∷ (□ ∀ (ep : w64) m uid ver val m_γ dig,
    ("%Hlook_map" ∷ ⌜ ms !! uint.nat ep = Some m ⌝ ∗
    "#Hsubmap" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some (m_γ, dig)) ∗
    "#Hin_cli" ∷ (uid, ver) ↪[m_γ]□ val)
    -∗
    (∃ label,
    "#His_label" ∷ is_vrf uid ver label ∗
    "%Hin_adtr" ∷ ⌜ m !! label = val ⌝)).

Definition auditEpoch_post adtr_pk seen_dig : iProp Σ :=
  □ ∀ adtr_γ,
  ("#His_pk" ∷ is_pk adtr_pk (adtr_sigpred adtr_γ))
  -∗
  (∃ adtr_st adtr_dig,
  "#Hcomm_st" ∷ comm_st.valid adtr_γ adtr_st ∗
  "%Hlook_adtr_dig" ∷ ⌜ adtr_st.(comm_st.digs) !!
    (uint.nat seen_dig.(SigDig.Epoch)) = Some adtr_dig ⌝ ∗
  "%Heq_dig" ∷ ⌜ seen_dig.(SigDig.Dig) = adtr_dig ⌝ ∗
  "%Hinv" ∷ ⌜ adtr_inv adtr_st.(comm_st.key_maps) ⌝).

Lemma wp_auditEpoch ptr_seen_dig seen_dig sl_serv_sig_pk (serv_sig_pk : list w8) ptr_adtr_cli adtr_cli sl_adtr_pk adtr_pk :
  {{{
    "#Hown_seen_dig" ∷ SigDig.own ptr_seen_dig seen_dig ∗
    "#His_seen_dig" ∷ is_SigDig seen_dig serv_sig_pk ∗
    "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded serv_sig_pk ∗
    "Hown_adtr_cli" ∷ advrpc.Client.own ptr_adtr_cli adtr_cli ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtr_pk byteT DfracDiscarded adtr_pk
  }}}
  auditEpoch #ptr_seen_dig (slice_val sl_serv_sig_pk) #ptr_adtr_cli (slice_val sl_adtr_pk)
  {{{
    ptr_err err, RET #ptr_err;
    "Hown_adtr_cli" ∷ advrpc.Client.own ptr_adtr_cli adtr_cli ∗
    "Herr" ∷ clientErr.own ptr_err err serv_sig_pk ∗
    if negb err.(clientErr.err) then auditEpoch_post adtr_pk seen_dig else True
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamedSuffix "Hown_seen_dig" "_seen".
  rewrite /auditEpoch. wp_pures.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_stdErr".
  wp_loadField.
  wp_apply (wp_callAdtrGet with "Hown_adtr_cli"). iIntros "* H". iNamed "H".
  wp_if_destruct.
  { iApply ("HΦ" $! _ (clientErr.mk None _)). by iFrame "∗#". }
  simpl. iNamed "H". iNamed "Hown_info". do 3 wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H0".
  iMod (struct_pointsto_persist with "H0") as "#H0".
  iDestruct (struct_fields_split with "H0") as "H1". iNamedSuffix "H1" "_serv".
  iClear "H0". do 3 wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H0".
  iMod (struct_pointsto_persist with "H0") as "#H0".
  iDestruct (struct_fields_split with "H0") as "H1". iNamedSuffix "H1" "_adtr".
  iClear "H0".
  wp_apply (wp_CheckSigDig _ (SigDig.mk _ _ _) with "[]"); [iFrame "#"|].
  iIntros (err0). iNamedSuffix 1 "_servSig". wp_if_destruct.
  { iApply ("HΦ" $! _ (clientErr.mk None _)). by iFrame "∗#". }
  wp_apply (wp_CheckSigDig _ (SigDig.mk _ _ _) with "[#]"); [iFrame "#"|].
  iIntros (err1). iNamedSuffix 1 "_adtrSig". wp_if_destruct.
  { iApply ("HΦ" $! _ (clientErr.mk None _)). by iFrame "∗#". }
  iDestruct ("Hgenie_servSig") as "[_ H]".
  iDestruct ("H" with "[//]") as "#His_servSig".
  iDestruct ("Hgenie_adtrSig") as "[_ H]".
  iDestruct ("H" with "[//]") as "#His_adtrSig".
  do 2 wp_loadField.
  wp_apply (wp_BytesEqual sl_Dig0 sl_Dig with "[$Hsl_Dig $Hsl_Dig_seen]").
  iIntros "_". wp_if_destruct.
  { wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
    iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_evid".
    wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
    iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_err".
    iApply ("HΦ" $! _ (clientErr.mk (Some
      (Evid.mk (SigDig.mk seen_dig.(SigDig.Epoch)
        adtrInfo.(AdtrEpochInfo.Dig) adtrInfo.(AdtrEpochInfo.ServSig))
      seen_dig)) _)).
    by iFrame "∗#". }
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_err".
  iApply ("HΦ" $! _ (clientErr.mk None _)).
  iFrame "∗#". iIntros (?) "!>". iNamed 1.
  iDestruct (is_sig_to_pred with "His_pk His_adtrSig") as "H".
  iNamed "H". apply PreSigDig.inj in Henc as <-. by iFrame "#%".
Qed.

Lemma mono_list_lb_idx_lookup γ l i a :
  (i < length l)%nat →
  mono_list_lb_own γ l -∗ mono_list_idx_own γ i a -∗ ⌜ l !! i = Some a ⌝.
Proof.
  iIntros (?) "Hlb0". iDestruct 1 as (??) "Hlb1".
  iDestruct (mono_list_lb_valid with "Hlb0 Hlb1") as %[Hpre|Hpre].
  - by rewrite (prefix_lookup_lt _ _ _ _ Hpre).
  - iPureIntro. by eapply prefix_lookup_Some.
Qed.

Lemma adtr_inv_prefix {l} l' :
  l' `prefix_of` l →
  adtr_inv l →
  adtr_inv l'.
Proof. Admitted.

Lemma wp_Client__Audit ptr_c c (adtrAddr : w64) sl_adtrPk adtr_pk :
  uint.Z c.(Client.next_epoch) > 0 →
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "#Hsl_adtrPk" ∷ own_slice_small sl_adtrPk byteT DfracDiscarded adtr_pk
  }}}
  Client__Audit #ptr_c #adtrAddr (slice_val sl_adtrPk)
  {{{
    ptr_err err, RET #ptr_err;
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Herr" ∷ clientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    if negb err.(clientErr.err) then
      ∀ adtr_γ,
      ("#His_pk" ∷ is_pk adtr_pk (adtr_sigpred adtr_γ))
      -∗
      ("#His_audit" ∷ is_audit c.(Client.γ) adtr_γ c.(Client.next_epoch))
    else True
  }}}.
Proof.
  iIntros (? Φ) "H HΦ". iNamed "H". rewrite /Client__Audit.
  wp_apply wp_Dial. iIntros (??). iNamedSuffix 1 "_adtr".
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "Herr0".
  wp_apply wp_ref_to; [val_ty|]. iIntros (ptr2_err0) "Hptr_err0".
  iNamed "Hown_cli". wp_loadField.
  wp_apply (wp_MapIter_fold _ _ _
    (λ sd_ptrs',
    ∃ ptr_err0 err0,
    "Hown_cli_adtr" ∷ advrpc.Client.own ptr_cli cli ∗
    "Herr" ∷ clientErr.own ptr_err0 err0 c.(Client.serv_sig_pk) ∗
    "Hptr_err0" ∷ ptr2_err0 ↦[ptrT] #ptr_err0 ∗
    if negb err0.(clientErr.err) then
      ∃ sd',
      "%Hdom" ∷ ⌜ dom sd_ptrs' = dom sd' ⌝ ∗
      "%Hsub" ∷ ⌜ sd' ⊆ sd ⌝ ∗
      "#Hpost" ∷ ([∗ map] x ∈ sd', auditEpoch_post adtr_pk x)
    else True)%I with "Hown_sd_map [$Hown_cli_adtr $Hptr_err0 Herr0]").
  { iDestruct (struct_fields_split with "Herr0") as "H". iNamed "H".
    iExists (clientErr.mk None false). iFrame. iExists ∅.
    iSplit; [done|]. iSplit. { iPureIntro. by eapply empty_subseteq. }
    naive_solver. }
  { clear. iIntros (??? Φ) "!> (Hpre&_&%Hlook_ptr) HΦ". iNamed "Hpre".
    wp_loadField.
    iDestruct (big_sepM2_lookup_l with "Hown_sd") as (?) "[%Hlook_dig Hown_dig]"; [exact Hlook_ptr|].
    iDestruct (big_sepM_lookup with "His_sd") as "H"; [exact Hlook_dig|].
    iNamed "H". wp_apply (wp_auditEpoch with "[$Hown_cli_adtr]"); [iFrame "#"|].
    iIntros (??) "Haudit". iNamedSuffix "Haudit" "1".
    iDestruct "Haudit" as "#Haudit".
    iNamedSuffix "Herr1" "1". wp_loadField. wp_if_destruct.
    - wp_store. iApply "HΦ". iExists ptr_err, err.
      rewrite /clientErr.own Heqb. by iFrame "∗#".
    - iApply "HΦ". iExists ptr_err0, err0.
      destruct err0.(clientErr.err) eqn:Heq_err0.
      + rewrite /clientErr.own Heq_err0. by iFrame "∗#".
      + rewrite /clientErr.own Heq_err0. iFrame.
        iNamedSuffix "Hpre" "_pre". iExists (<[k:=x2]>sd').
        iIntros "!>". iSplit. { iPureIntro. set_solver. }
        iSplit. { iPureIntro. by apply insert_subseteq_l. }
        iApply big_sepM_insert_2; iFrame "#". }
  iIntros "[Hown_sd_maps Hpost]". iNamed "Hpost". iClear "Hown_cli_adtr".
  iDestruct (mono_list_lb_own_get with "Hown_epochs") as "#His_epochs".
  wp_load. iApply "HΦ". iFrame "∗#%".
  destruct err0.(clientErr.err); [done|].
  iIntros "!>". iIntros (?). iNamed 1. iNamed "Hpost".
  iDestruct (big_sepM2_dom with "Hown_sd") as %Hdom1.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as ->.
  { by rewrite -Hdom -Hdom1. }

  (* process last ep to fill is_audit adtr maps. *)
  destruct (last ms) eqn:Hlast; rewrite last_lookup in Hlast.
  2: { exfalso. rewrite lookup_ge_None in Hlast. word. }
  opose proof (Hlast_some _ _) as [[[??]?]?]; [done|]. simplify_eq/=.
  rewrite Heq_next_ep in Hlast.
  replace (pred (uint.nat c.(Client.next_epoch))) with
    (Z.to_nat (uint.Z c.(Client.next_epoch) - 1%Z)) in Hlast; [|word].
  iDestruct (big_sepL_lookup with "His_maps") as "H"; [exact Hlast|]. iNamed "H".
  iDestruct (big_sepM_lookup with "Hpost") as "H"; [exact Hlook_sd|].
  iSpecialize ("H" with "His_pk"). iNamed "H". iNamed "Hcomm_st".
  iDestruct (big_sepM_lookup with "His_sd") as "H"; [exact Hlook_sd|].
  iNamed "H".

  iExists (take (uint.nat c.(Client.next_epoch)) adtr_st.(comm_st.key_maps)).
  iSplit. { iApply (mono_list_lb_own_le with "Hmaps"). apply prefix_take. }
  iDestruct (big_sepL2_length with "Hdigs") as %?.
  iSplit.
  { iPureIntro. apply lookup_lt_Some in Hlook_adtr_dig.
    rewrite Heq_ep in Hlook_adtr_dig. rewrite length_take_le; [done|word]. }
  iSplit. { iPureIntro. refine (adtr_inv_prefix _ _ Hinv). apply prefix_take. }
  iIntros "!> *". iNamed 1.

  (* process the ep in the wand precond. *)
  (*
  iDestruct (mono_list_lb_idx_lookup with "His_epochs Hsubmap") as "H".
  { apply lookup_lt_Some in Hlook_map. rewrite length_take in Hlook_map.
    rewrite length_fmap. word. }
    *)
  iClear (Hlook_sd Heq_sd_dig Hlook_adtr_dig Heq_dig Hinv Heq_ep) "His_dig".
Admitted.

Lemma wp_newClient (uid servAddr : w64) sl_servSigPk servSigPk (servVrfPk : loc) :
  {{{
    "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded servSigPk
  }}}
  newClient #uid #servAddr (slice_val sl_servSigPk) #servVrfPk
  {{{
    ptr_cli cli_γ r1 r2, RET #ptr_cli;
    "Hown_cli" ∷ Client.own ptr_cli (Client.mk cli_γ uid (W64 0) (W64 0) r1 servSigPk r2)
  }}}.
Proof.

(* TODO: wanna know how hard it is to prove wand.
there might be gotchas. *)

End specs.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma get_audit_msv cli_γ uid ep lat adtr_γ aud_ep :
  uint.Z ep < uint.Z aud_ep →
  ("#His_key" ∷ is_other_key cli_γ uid ep lat ∗
  "#His_audit" ∷ is_audit cli_γ adtr_γ aud_ep) -∗
  msv adtr_γ ep uid lat.
Proof.
  intros ?. iNamed 1. iNamed "His_audit". iNamed "His_key". iNamedSuffix "Hbound" "_bnd".
  list_elem ms (uint.nat ep) as m.
  iDestruct (mono_list_idx_own_get with "Hadtr_maps") as "Hadtr_map"; [exact Hm_lookup|].
  iFrame "#". iSplit.
  - iApply big_sepL_forall.  iIntros "* %Hlook_val".
    iDestruct (big_sepL_lookup with "Hhist") as "H"; [exact Hlook_val|]. iNamed "H".
    iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_map $His_label]") as %?; [done|].
    iFrame "#%".
  - by iDestruct ("Hmap_transf" with "[$Hsubmap $Hin_map_bnd $His_label_bnd]") as %?.
Qed.

End derived.
