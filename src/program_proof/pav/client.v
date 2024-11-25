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
    serv_vrf_pk: list w8;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; next_ver; next_epoch; serv_γ; serv_sig_pk; serv_vrf_pk>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ digs ptr_sd sd_refs sd ptr_serv_cli serv_cli sl_serv_sig_pk ptr_vrf_pk,
  (* seenDigs (sd). *)
  "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
  "#Hptr_sd" ∷ ptr ↦[Client :: "seenDigs"]□ #ptr_sd ∗
  "#Hown_sd" ∷ ([∗ map] l;x ∈ sd_refs;sd, SigDig.own l x) ∗
  "#His_sd" ∷ ([∗ map] ep ↦ x ∈ sd,
    "%Heq_ep" ∷ ⌜ ep = x.(SigDig.Epoch) ⌝ ∗
    "#His_sigdig" ∷ is_SigDig x obj.(serv_sig_pk)) ∗
  (* uid, next_ver, next_epoch. *)
  "#Hptr_uid" ∷ ptr ↦[Client :: "uid"]□ #obj.(uid) ∗
  "Hptr_nextVer" ∷ ptr ↦[Client :: "nextVer"] #obj.(next_ver) ∗
  "Hptr_nextEpoch" ∷ ptr ↦[Client :: "nextEpoch"] #obj.(next_epoch) ∗
  (* server info. *)
  "Hown_servCli" ∷ advrpc.Client.own ptr_serv_cli serv_cli ∗
  "#Hptr_servCli" ∷ ptr ↦[Client :: "servCli"]□ #ptr_serv_cli ∗
  "#Hptr_servSigPk" ∷ ptr ↦[Client :: "servSigPk"]□ (slice_val sl_serv_sig_pk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded obj.(serv_sig_pk) ∗
  "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk obj.(serv_vrf_pk) ∗
  "#Hptr_servVrfPk" ∷ ptr ↦[Client :: "servVrfPk"]□ #ptr_vrf_pk ∗
  (* digs ghost state. *)
  "Hown_digs" ∷ mono_list_auth_own obj.(γ) 1 digs ∗
  "%Hagree_digs_sd" ∷ ⌜ ∀ (ep : w64) dig, digs !! (uint.nat ep) = Some (Some dig) →
    ∃ sig, sd !! ep = Some (SigDig.mk ep dig sig) ⌝ ∗
  "%Hlast_digs" ∷ ⌜ ∀ m, last digs = Some m → is_Some m ⌝ ∗
  "%Hlen_digs" ∷ ⌜ length digs = uint.nat obj.(next_epoch) ⌝.

End defs.
End Client.

Module ClientErr.
Record t :=
  mk {
    Evid: option Evid.t;
    Err: bool;
  }.
Section defs.
Context `{!heapGS Σ}.
Definition own (ptr : loc) (obj : t) (pk : list w8) : iProp Σ :=
  ∃ (ptr_evid : loc),
  "Hptr_evid" ∷ ptr ↦[ClientErr :: "Evid"] #ptr_evid ∗
  "Hptr_err" ∷ ptr ↦[ClientErr :: "Err"] #obj.(Err) ∗
  "Hevid" ∷ match obj.(Evid) with
  | Some e =>
    "Hown_evid" ∷ Evid.own ptr_evid e ∗
    "#His_evid" ∷ is_Evid e pk
  | None => True
  end.
End defs.
End ClientErr.

Section wps.
Context `{!heapGS Σ, !pavG Σ}.

Lemma wp_checkDig sl_sig_pk (sig_pk : list w8) ptr_sd (sd_refs : gmap w64 loc) sd ptr_dig dig :
  {{{
    "#Hsl_sig_pk" ∷ own_slice_small sl_sig_pk byteT DfracDiscarded sig_pk ∗
    "#Hown_sd" ∷ ([∗ map] l;x ∈ sd_refs;sd, SigDig.own l x) ∗
    "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
    "#His_sd" ∷ ([∗ map] ep ↦ x ∈ sd,
      "%Heq_ep" ∷ ⌜ ep = x.(SigDig.Epoch) ⌝ ∗
      "#His_sigdig" ∷ is_SigDig x sig_pk) ∗
    "#Hown_dig" ∷ SigDig.own ptr_dig dig
  }}}
  checkDig (slice_val sl_sig_pk) #ptr_sd #ptr_dig
  {{{
    err ptr_err, RET #ptr_err;
    "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
    "Hown_err" ∷ ClientErr.own ptr_err err sig_pk ∗
    "Herr" ∷ (if err.(ClientErr.Err) then True else
      "#His_dig" ∷ is_SigDig dig sig_pk ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z (word.add dig.(SigDig.Epoch) (W64 1)) =
        (uint.Z dig.(SigDig.Epoch) + 1)%Z ⌝ ∗
      "%Heq_old" ∷ ⌜ ∀ old, sd !! dig.(SigDig.Epoch) = Some old →
        dig.(SigDig.Dig) = old.(SigDig.Dig) ⌝)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) sig_pk) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }
  wp_apply (wp_CheckSigDig with "[$Hown_dig $Hsl_sig_pk]").
  iIntros "*". iNamedSuffix 1 "_sigdig".
  wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  iDestruct "Hgenie_sigdig" as "[_ H]".
  iDestruct ("H" with "[//]") as "#His_sigdig".
  iPoseProof "Hown_dig" as "H". iNamed "H".
  wp_loadField. wp_apply wp_SumNoOverflow. wp_if_destruct.
  { iApply "HΦ". by iFrame. }
  wp_loadField. wp_apply (wp_MapGet with "Hown_sd_refs").
  iIntros "* [%Hlook_sd_refs Hown_sd_refs]". destruct ok.
  { apply map_get_true in Hlook_sd_refs.
    iDestruct (big_sepM2_lookup_l_some with "Hown_sd") as %[? Hlook_sd];
      [exact Hlook_sd_refs|].
    iDestruct (big_sepM2_lookup with "Hown_sd") as "Hown_dig_old";
      [exact Hlook_sd_refs|exact Hlook_sd|].
    iDestruct (big_sepM_lookup with "His_sd") as "His_dig_old";
      [exact Hlook_sd|].
    iNamedSuffix "His_dig_old" "_old".
    iPoseProof "Hown_dig_old" as "H". iNamedSuffix "H" "_old".
    do 2 wp_loadField.
    wp_apply (wp_BytesEqual sl_Dig0 sl_Dig with "[$Hsl_Dig $Hsl_Dig_old]").
    iIntros "_". iClear "Hown_std_err". wp_if_destruct.
    - wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
      iDestruct (struct_fields_split with "H") as "H". iNamed "H".
      wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
      iDestruct (struct_fields_split with "H") as "H". iNamed "H".
      iApply ("HΦ" $! (ClientErr.mk (Some (Evid.mk _ _)) true)).
      by iFrame "∗ Hown_dig Hown_dig_old His_sigdig His_sigdig_old".
    - wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
      iDestruct (struct_fields_split with "H") as "H". iNamed "H".
      iApply ("HΦ" $! (ClientErr.mk None false)). iFrame "∗#%".
      iPureIntro. naive_solver. }
  apply map_get_false in Hlook_sd_refs as [Hlook_sd_refs _].
  iDestruct (big_sepM2_lookup_l_none with "Hown_sd") as %Hlook_sd;
    [exact Hlook_sd_refs|].
  iClear "Hown_std_err". wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iApply ("HΦ" $! (ClientErr.mk None false)). iFrame "∗#%".
  iPureIntro. naive_solver.
Qed.

Lemma wp_checkLabel ptr_vrf_pk vrf_pk sl_proof uid ver (proof : list w8) :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_proof" ∷ own_slice_small sl_proof byteT DfracDiscarded proof
  }}}
  checkLabel #ptr_vrf_pk #uid #ver (slice_val sl_proof)
  {{{
    sl_label (label : list w8) (err : bool), RET (slice_val sl_label, #err);
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT (DfracOwn 1) label ∗
    "Herr" ∷ (if err then True else is_map_label vrf_pk uid ver label)
  }}}.
Proof. Admitted.

Lemma wp_checkMemb ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_memb memb :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hown_memb" ∷ Memb.own ptr_memb memb
  }}}
  checkMemb #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_memb
  {{{
    (err : bool), RET #err;
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hown_memb" ∷ Memb.own ptr_memb memb ∗
    "Herr" ∷ (if err then True else
      ∃ label comm,
      "#His_label" ∷ is_map_label vrf_pk uid ver label ∗
      "#His_commit" ∷ is_commit memb.(Memb.PkOpen).(CommitOpen.Val) comm ∗
      "#Hhas_merk_proof" ∷ is_merkle_entry label
        (Some (MapValPre.encodesF $ MapValPre.mk memb.(Memb.EpochAdded) comm)) dig)
  }}}.
Proof. Admitted.

Lemma wp_checkMembHide ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_memb_hide memb_hide :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hown_memb_hide" ∷ MembHide.own ptr_memb_hide memb_hide
  }}}
  checkMembHide #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_memb_hide
  {{{
    (err : bool) label, RET #err;
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hown_memb_hide" ∷ MembHide.own ptr_memb_hide memb_hide ∗
    "Herr" ∷ (if err then True else
      "#His_label" ∷ is_map_label vrf_pk uid ver label ∗
      "#Hhas_merk_proof" ∷ is_merkle_entry label (Some memb_hide.(MembHide.MapVal)) dig)
  }}}.
Proof. Admitted.

Lemma wp_checkHist ptr_vrf_pk vrf_pk (uid : w64) sl_dig (dig : list w8) sl_hist (histref : list loc) hist :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "#Hsl_hist" ∷ own_slice_small sl_hist ptrT DfracDiscarded histref ∗
    "Hown_hist" ∷ ([∗ list] ptr_memb_hide;memb_hide ∈ histref;hist,
      MembHide.own ptr_memb_hide memb_hide)
  }}}
  checkHist #ptr_vrf_pk #uid (slice_val sl_dig) (slice_val sl_hist)
  {{{
    (err : bool), RET #err;
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hown_hist" ∷ ([∗ list] ptr_memb_hide;memb_hide ∈ histref;hist,
      MembHide.own ptr_memb_hide memb_hide) ∗
    "Herr" ∷ (if err then True else
      ([∗ list] ver ↦ val ∈ (MembHide.MapVal <$> hist),
        ∃ label,
        "#His_label" ∷ is_map_label vrf_pk uid (W64 ver) label ∗
        "#Hhas_merk_proof" ∷ is_merkle_entry label (Some val) dig))
  }}}.
Proof. Admitted.

Lemma wp_checkNonMemb ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_non_memb non_memb :
  {{{
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hown_non_memb" ∷ NonMemb.own ptr_non_memb non_memb
  }}}
  checkNonMemb #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_non_memb
  {{{
    (err : bool) label, RET #err;
    "Hown_vrf_pk" ∷ own_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hown_non_memb" ∷ NonMemb.own ptr_non_memb non_memb ∗
    "Herr" ∷ (if err then True else
      "#His_label" ∷ is_map_label vrf_pk uid ver label ∗
      "#Hhas_merk_proof" ∷ is_merkle_entry label None dig)
  }}}.
Proof. Admitted.

Definition is_cli_entry cli_γ serv_vrf_pk (ep : w64) uid ver val : iProp Σ :=
  ∃ dig label,
  "#His_dig" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some dig) ∗
  "#His_label" ∷ is_map_label serv_vrf_pk uid ver label ∗
  "#Hhas_merk_proof" ∷ is_merkle_entry label val dig.

Definition is_put_post cli_γ serv_vrf_pk uid ver ep pk : iProp Σ :=
  ∃ commit,
  "#Hcommit" ∷ is_commit pk commit ∗
  "#His_lat" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid ver
    (Some (MapValPre.encodesF (MapValPre.mk ep commit))) ∗
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (word.add ver (W64 1)) None.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    "Herr" ∷ if err.(ClientErr.Err) then
      "Hown_cli" ∷ Client.own ptr_c c
    else
      let new_c := set Client.next_ver (λ x, (word.add x (W64 1)))
        (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_put_post" ∷ is_put_post c.(Client.γ) c.(Client.serv_vrf_pk)
        c.(Client.uid) c.(Client.next_ver) ep pk ∗
      "%Hnoof_ver" ∷ ⌜ uint.Z (word.add c.(Client.next_ver) (W64 1)) = (uint.Z c.(Client.next_ver) + 1)%Z ⌝ ∗
      "%Hnoof_eq" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) ≤ uint.Z ep ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_cli". rewrite /Client__Put.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv_sig_pk)) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }
  do 2 wp_loadField.
  wp_apply (wp_CallServPut with "[$Hown_servCli $Hsl_pk]").
  iIntros (err0) "*". iNamed 1. destruct err0.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamed "Herr". iPoseProof "Hown_dig" as "H". iNamed "H".
  (* TODO: wp_pures takes a long time for some reason. *)
  wp_pures. do 2 wp_loadField.
  wp_apply (wp_checkDig with "[$Hsl_servSigPk $Hown_sd $Hown_sd_refs $His_sd $Hown_dig]").
  iIntros (err1) "*". iNamed 1. iNamedSuffix "Hown_err" "1". wp_loadField.
  destruct (err1.(ClientErr.Err)).
  { wp_pures. iApply ("HΦ" $! (ClientErr.mk _ true)).
    iClear "Hown_std_err". by iFrame "∗#%". }
  iClear "Hptr_evid1 Hptr_err1 Hevid1". iNamed "Herr".
  do 2 wp_loadField. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rename Heqb into Hfresh_ep. do 4 wp_loadField.
  wp_apply (wp_checkMemb with "[$Hown_vrf_pk $Hsl_Dig $Hown_memb]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamedSuffix "Herr" "_memb". iNamed "Hown_memb".
  do 2 wp_loadField. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rewrite -Heqb0 {Heqb0}. iNamedSuffix "Hown_pk_open" "_open0". do 2 wp_loadField.
  wp_apply (wp_BytesEqual sl_pk sl_val with "[$Hsl_pk $Hsl_val_open0]").
  iIntros "[Hsl_pk _]". wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rewrite -Heqb {Heqb}. do 4 wp_loadField.
  wp_apply (wp_checkNonMemb with "[$Hown_vrf_pk $Hsl_Dig $Hown_nonmemb]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamedSuffix "Herr" "_nonmemb". do 2 wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_sd_refs]").
  iIntros "Hown_sd_refs". wp_loadField. wp_storeField. wp_loadField.
  wp_apply wp_SumAssumeNoOverflow. iIntros "%Hnoof_ver".
  wp_storeField. wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_pures. iApply ("HΦ" $! (ClientErr.mk None false)).
  iDestruct (big_sepM2_insert_2 (λ _ x y, SigDig.own x y) _ _ dig.(SigDig.Epoch)
    with "Hown_dig Hown_sd") as "Hnew_own_sd".
  iDestruct (big_sepM_insert_2 (λ _ x, is_SigDig x _) _ dig.(SigDig.Epoch)
    with "His_dig His_sd") as "Hnew_is_sd".
  iClear "Hown_sd His_sd Hown_dig His_dig".

  (* grow ghost digs. *)
  set (digs ++ (replicate (uint.nat dig.(SigDig.Epoch) - length digs) None) ++
    [Some dig.(SigDig.Dig)]) as new_digs.
  iMod (mono_list_auth_own_update new_digs with "Hown_digs") as "[Hown_digs #Hlb]".
  { by apply prefix_app_r. }
  iDestruct (mono_list_idx_own_get (uint.nat dig.(SigDig.Epoch)) with "Hlb") as "#Hlook_gdigs".
  { rewrite lookup_app_r; [|word].
    rewrite lookup_app_r; rewrite length_replicate; [|done].
    apply list_lookup_singleton_Some. split; [lia|done]. }
  iFrame "∗#". iIntros "!> !% //".
  repeat try split; try word.
  - intros ep ? Hlook_digs.
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[? Hlook_digs]].
    { rewrite lookup_insert_ne. 2: { apply lookup_lt_Some in Hlook_digs. word. }
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd]. naive_solver. }
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[Heq0 Hlook_digs]].
    { apply lookup_replicate in Hlook_digs. naive_solver. }
    apply list_lookup_singleton_Some in Hlook_digs as [Heq1 Hlook_digs].
    rewrite length_replicate in Heq0 Heq1.
    assert (ep = dig.(SigDig.Epoch)) as -> by word.
    rewrite lookup_insert. destruct dig. naive_solver.
  - subst new_digs. rewrite app_assoc last_snoc. naive_solver.
  - rewrite !length_app length_replicate. simpl. word.
Qed.

Definition is_selfmon_post cli_γ serv_vrf_pk uid ver (ep : w64) : iProp Σ :=
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid ver None.

Lemma wp_Client__SelfMon ptr_c c :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    "Herr" ∷ if err.(ClientErr.Err) then
      "Hown_cli" ∷ Client.own ptr_c c
    else
      let new_c := (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "#His_selfmon_post" ∷ is_selfmon_post c.(Client.γ) c.(Client.serv_vrf_pk)
        c.(Client.uid) c.(Client.next_ver) ep ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_cli". rewrite /Client__SelfMon.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv_sig_pk)) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }
  do 2 wp_loadField. wp_apply (wp_CallServSelfMon with "[$Hown_servCli]").
  iIntros (err0) "*". iNamed 1. destruct err0.
  (* TODO: seems like an iFrame bug that i have to do ∗∗. *)
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamed "Herr". iPoseProof "Hown_dig" as "H". iNamed "H". do 2 wp_loadField.
  wp_apply (wp_checkDig with "[$Hsl_servSigPk $Hown_sd $Hown_sd_refs $His_sd $Hown_dig]").
  iIntros (err1) "*". iNamed 1. iNamedSuffix "Hown_err" "1". wp_loadField.
  destruct (err1.(ClientErr.Err)).
  { wp_pures. iApply ("HΦ" $! (ClientErr.mk _ true)).
    iClear "Hown_std_err". by iFrame "∗#%". }
  iClear "Hptr_evid1 Hptr_err1 Hevid1". iNamed "Herr". wp_loadField.
  wp_apply (wp_and with "[Hptr_nextEpoch]").
  { iNamedAccu. }
  { wp_pures. by rewrite -bool_decide_not. }
  { iIntros (?). iNamed 1. do 2 wp_loadField. wp_pures. by iFrame. }
  iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rename Heqb into Hfresh_ep. do 4 wp_loadField.
  wp_apply (wp_checkNonMemb with "[$Hown_vrf_pk $Hsl_Dig $Hown_nonmemb]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  do 2 wp_loadField. wp_apply (wp_MapInsert_to_val with "[$Hown_sd_refs]").
  iIntros "Hown_sd_refs". wp_loadField. wp_storeField. wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_pures. iApply ("HΦ" $! (ClientErr.mk None false)).
  iFrame "Evid Err Herr".
  (* our impl always inserts, even if the dig was already there. *)
  iDestruct (big_sepM2_insert_2 (λ _ x y, SigDig.own x y) _ _ dig.(SigDig.Epoch)
    with "Hown_dig Hown_sd") as "Hnew_own_sd".
  iDestruct (big_sepM_insert_2 (λ _ x, is_SigDig x _) _ dig.(SigDig.Epoch)
    with "His_dig His_sd") as "Hnew_is_sd".
  iClear "Hown_sd His_sd Hown_dig His_dig".
  iFrame "Hown_sd_refs Hptr_nextVer Hown_cli Hptr_nextEpoch Hown_vrf_pk #".
  destruct (decide ((S $ uint.nat dig.(SigDig.Epoch)) = length digs)).
  (* case 1: new dig is in old ghost digs. *)
  { list_elem digs (pred $ length digs) as last_dig.
    rewrite -last_lookup in Hlast_dig_lookup.
    opose proof (Hlast_digs _ Hlast_dig_lookup) as [? ->].
    rewrite last_lookup in Hlast_dig_lookup.
    replace (pred (length digs)) with (uint.nat dig.(SigDig.Epoch)) in Hlast_dig_lookup; [|word].
    opose proof (Hagree_digs_sd _ _ Hlast_dig_lookup) as [? Hlook_sd].
    opose proof (Heq_old _ Hlook_sd) as Heq_dig. simplify_eq/=.
    iDestruct (mono_list_idx_own_get _ _ Hlast_dig_lookup with "[Hown_digs]") as "#Hlook_gdigs".
    { by iApply mono_list_lb_own_get. }
    iFrame "Hlook_gdigs Hown_digs %". iIntros "!>". repeat try iSplit; [|word..].
    iIntros (ep ? Hlook_digs) "!%".
    opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd2].
    destruct (decide (ep = dig.(SigDig.Epoch))) as [->|].
    + rewrite lookup_insert. destruct dig. naive_solver.
    + rewrite lookup_insert_ne; [naive_solver|done]. }
  (* case 2: new dig is not in old ghost digs. update ghost state. *)
  assert (uint.nat dig.(SigDig.Epoch) ≥ length digs) as ?.
  { apply not_and_l_alt in Hfresh_ep.
    destruct Hfresh_ep as [Hep|[Hep0 Hep1]].
    + apply Classical_Prop.NNPP in Hep. apply inv_litint in Hep. word.
    + apply u64_val_ne in Hep1.
      replace (uint.Z (word.sub _ _)) with
        (uint.Z c.(Client.next_epoch) - 1) in Hep0 by word. word. }
  set (digs ++ (replicate (uint.nat dig.(SigDig.Epoch) - length digs) None) ++
    [Some dig.(SigDig.Dig)]) as new_digs.
  iMod (mono_list_auth_own_update new_digs with "Hown_digs") as "[Hown_digs #Hlb]".
  { by apply prefix_app_r. }
  iDestruct (mono_list_idx_own_get (uint.nat dig.(SigDig.Epoch)) with "Hlb") as "#Hlook_gdigs".
  { rewrite lookup_app_r; [|word].
    rewrite lookup_app_r; rewrite length_replicate; [|done].
    apply list_lookup_singleton_Some. split; [lia|done]. }
  iFrame "∗#". iIntros "!> !%". repeat try split; try word.
  - intros ep ? Hlook_digs.
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[? Hlook_digs]].
    { rewrite lookup_insert_ne. 2: { apply lookup_lt_Some in Hlook_digs. word. }
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd]. naive_solver. }
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[Heq0 Hlook_digs]].
    { apply lookup_replicate in Hlook_digs. naive_solver. }
    apply list_lookup_singleton_Some in Hlook_digs as [Heq1 Hlook_digs].
    rewrite length_replicate in Heq0 Heq1.
    assert (ep = dig.(SigDig.Epoch)) as -> by word.
    rewrite lookup_insert. destruct dig. naive_solver.
  - subst new_digs. rewrite app_assoc last_snoc. naive_solver.
  - rewrite !length_app length_replicate. simpl. word.
Qed.

Definition is_get_post_Some cli_γ serv_vrf_pk uid (ep : w64) pk : iProp Σ :=
  ∃ hist ep' commit,
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ hist,
    is_cli_entry cli_γ serv_vrf_pk ep uid ver (Some val)) ∗
  "#Hcommit" ∷ is_commit pk commit ∗
  "#His_lat" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (W64 $ length hist)
    (Some (MapValPre.encodesF (MapValPre.mk ep' commit))) ∗
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (word.add (length hist) (W64 1)) None.

Definition is_get_post_None cli_γ serv_vrf_pk uid (ep : w64) : iProp Σ :=
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (W64 0) None.

Lemma wp_Client__Get ptr_c c uid :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    err (is_reg : bool) sl_pk (ep : w64) ptr_err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    "Herr" ∷ (if err.(ClientErr.Err) then "Hown_cli" ∷ Client.own ptr_c c else
      let new_c := (set Client.next_epoch (λ _, word.add ep (W64 1)) c) in
      "Hown_cli" ∷ Client.own ptr_c new_c ∗
      "%Hnoof_ep" ∷ ⌜ uint.Z (word.add ep (W64 1)) = (uint.Z ep + 1)%Z ⌝ ∗
      "%Hgt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) - 1 ≤ uint.Z ep ⌝ ∗
      "Hreg" ∷ (if is_reg
        then
        ∃ pk,
        "Hsl_pk" ∷ own_slice_small sl_pk byteT (DfracOwn 1) pk ∗
        "#His_get_post" ∷ is_get_post_Some c.(Client.γ) c.(Client.serv_vrf_pk) uid ep pk
        else
        "#His_get_post" ∷ is_get_post_None c.(Client.γ) c.(Client.serv_vrf_pk) uid ep))
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_cli". rewrite /Client__Get.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv_sig_pk)) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }
  wp_loadField. wp_apply (wp_CallServGet with "[$Hown_servCli]").
  (* TODO: prob should not have to do this to get HΦ to work. *)
  replace (slice.nil) with (slice_val Slice.nil); [|done].
  iIntros (err0) "*". iNamed 1. destruct err0.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamed "Herr". iPoseProof "Hown_dig" as "H". iNamed "H".
  (* TODO: wp_pures takes a long time for some reason. *)
  wp_pures. do 2 wp_loadField.
  wp_apply (wp_checkDig with "[$Hsl_servSigPk $Hown_sd $Hown_sd_refs $His_sd $Hown_dig]").
  iIntros (err1) "*". iNamed 1. iNamedSuffix "Hown_err" "1". wp_loadField.
  destruct (err1.(ClientErr.Err)).
  { wp_pures. iApply ("HΦ" $! (ClientErr.mk _ true)).
    iClear "Hown_std_err". by iFrame "∗#%". }
  iClear "Hptr_evid1 Hptr_err1 Hevid1". iNamed "Herr".
  wp_loadField. wp_apply (wp_and with "[Hptr_nextEpoch]").
  { iNamedAccu. }
  { wp_pures. by rewrite -bool_decide_not. }
  { iIntros (?). iNamed 1. do 2 wp_loadField. wp_pures. by iFrame. }
  iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rename Heqb into Hfresh_ep. do 2 wp_loadField.
  iMod (own_slice_small_persist with "Hsl_hist") as "#Hsl_hist".
  wp_apply (wp_checkHist with "[$Hown_vrf_pk $Hsl_Dig $Hsl_hist $Hown_hist]").
  iIntros (?). iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  clear Heqb. iDestruct "Herr" as "#Hhist". wp_apply wp_slice_len.
  wp_apply wp_and.
  { iNamedAccu. }
  { by wp_pures. }
  { iIntros "_ _". wp_pures. iIntros "!> !%". split; [|done].
    (* TODO: this negb <-> bool_decide reasoning should be automated. *)
    case_bool_decide; simplify_eq/=.
    { done. }
    { destruct is_reg; done. } }
  Unshelve. 2: { apply _. }
  iIntros "_". wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  rename Heqb into Hconsis_is_reg.
  wp_bind (if: #is_reg then _ else _)%E.
  iApply (wp_wand _ _ _
    (λ v, ∃ (b : bool), ⌜ v = #b ⌝ ∗ _ ∗ (if b then _ else (if is_reg then _ else _)))%I
    with "[Hown_vrf_pk Hown_memb]").
  { wp_if_destruct.
    - do 2 wp_loadField.
      wp_apply (wp_checkMemb with "[$Hown_vrf_pk $Hsl_Dig $Hown_memb]").
      iIntros "*". iNamed 1. iExists _. iSplit; [done|].
      (* TODO: iris-named-prop names got screwed up thru string unification. *)
      rewrite /named. iSplitL "Hown_vrf_pk Hown_memb"; iAccu.
    - iIntros "!>". iExists _. iSplit; [done|]. iSplitL; [iFrame|iAccu]. }
  iIntros "* [% (-> & (Hown_vrf_pk & Hown_memb) & Hcheck_memb)]".
  wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_boundVer) "Hptr_boundVer".
  wp_apply (wp_If_join_evar
    (λ b, _ ↦[_] #((if b then _ else _) : w64))%I
    with "[Hptr_boundVer]").
  { iIntros "* ->". wp_if_destruct.
    - wp_store. iIntros "!>". iSplit; [done|iAccu].
    - iIntros "!>". iSplit; [done|iAccu]. }
  iIntros "Hptr_boundVer". wp_loadField. wp_load. wp_loadField.
  wp_apply (wp_checkNonMemb with "[$Hown_vrf_pk $Hsl_Dig $Hown_nonmemb]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". by iFrame "∗∗#%". }
  iNamedSuffix "Herr" "_nonmemb".
  do 2 wp_loadField. wp_apply (wp_MapInsert_to_val with "[$Hown_sd_refs]").
  iIntros "Hown_sd_refs". wp_loadField. wp_storeField.
  iNamed "Hown_memb". iNamed "Hown_pk_open". rewrite Hpk_dfrac. do 3 wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".

  wp_pures. iApply ("HΦ" $! (ClientErr.mk None false)).
  iDestruct (big_sepM2_insert_2 (λ _ x y, SigDig.own x y) _ _ dig.(SigDig.Epoch)
    with "Hown_dig Hown_sd") as "Hnew_own_sd".
  iDestruct (big_sepM_insert_2 (λ _ x, is_SigDig x _) _ dig.(SigDig.Epoch)
    with "His_dig His_sd") as "Hnew_is_sd".
  iClear "Hown_sd His_sd Hown_dig His_dig".
  iFrame "Evid Err Hown_sd_refs Hptr_nextVer Hown_cli Hptr_nextEpoch
    Hown_vrf_pk #".
  iAssert (⌜ W64 $ length (MembHide.MapVal <$> hist) = sl_hist.(Slice.sz) ⌝)%I as %Hlen_hist.
  { iDestruct (own_slice_small_sz with "Hsl_hist") as %?.
    iDestruct (big_sepL2_length with "Hown_hist") as %?.
    rewrite length_fmap. word. }
  destruct (decide ((S $ uint.nat dig.(SigDig.Epoch)) = length digs)).
  (* case 1: new dig is in old ghost digs. *)
  { list_elem digs (pred $ length digs) as last_dig.
    rewrite -last_lookup in Hlast_dig_lookup.
    opose proof (Hlast_digs _ Hlast_dig_lookup) as [? ->].
    rewrite last_lookup in Hlast_dig_lookup.
    replace (pred (length digs)) with (uint.nat dig.(SigDig.Epoch)) in Hlast_dig_lookup; [|word].
    opose proof (Hagree_digs_sd _ _ Hlast_dig_lookup) as [? Hlook_sd].
    opose proof (Heq_old _ Hlook_sd) as Heq_dig. simplify_eq/=.
    iDestruct (mono_list_idx_own_get _ _ Hlast_dig_lookup with "[Hown_digs]") as "#Hlook_gdigs".
    { by iApply mono_list_lb_own_get. }
    iFrame "Hown_digs %". iIntros "!>".
    repeat try iSplit; try word; [|destruct is_reg].
    - iIntros (ep ? Hlook_digs) "!%".
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd2].
      destruct (decide (ep = dig.(SigDig.Epoch))) as [->|].
      + rewrite lookup_insert. destruct dig. naive_solver.
      + rewrite lookup_insert_ne; [naive_solver|done].
    - iDestruct "Hcheck_memb" as
        (??) "(#His_label_memb & #His_commit_memb & #Hhas_merk_proof_memb)".
      iFrame "Hsl_val Hhas_merk_proof_memb Hhas_merk_proof_nonmemb".
      iExists (MembHide.MapVal <$> hist).
      rewrite Hlen_hist. iFrame "#". iApply (big_sepL_impl with "Hhist").
      iIntros "!> * _ H". iNamedSuffix "H" "_hist". iFrame "#".
    - iFrame "#". }

  (* case 2: new dig is not in old ghost digs. update ghost state. *)
  assert (uint.nat dig.(SigDig.Epoch) ≥ length digs) as ?.
  { apply not_and_l_alt in Hfresh_ep.
    destruct Hfresh_ep as [Hep|[Hep0 Hep1]].
    + apply Classical_Prop.NNPP in Hep. apply inv_litint in Hep. word.
    + apply u64_val_ne in Hep1.
      replace (uint.Z (word.sub _ _)) with
        (uint.Z c.(Client.next_epoch) - 1) in Hep0 by word. word. }
  set (digs ++ (replicate (uint.nat dig.(SigDig.Epoch) - length digs) None) ++
    [Some dig.(SigDig.Dig)]) as new_digs.
  iMod (mono_list_auth_own_update new_digs with "Hown_digs") as "[Hown_digs #Hlb]".
  { by apply prefix_app_r. }
  iDestruct (mono_list_idx_own_get (uint.nat dig.(SigDig.Epoch)) with "Hlb") as "#Hlook_gdigs".
  { rewrite lookup_app_r; [|word].
    rewrite lookup_app_r; rewrite length_replicate; [|done].
    apply list_lookup_singleton_Some. split; [lia|done]. }
  iFrame "∗#". iModIntro. repeat try iSplit; try word; [iPureIntro..|destruct is_reg].
  - intros ep ? Hlook_digs.
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[? Hlook_digs]].
    { rewrite lookup_insert_ne. 2: { apply lookup_lt_Some in Hlook_digs. word. }
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd]. naive_solver. }
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[Heq0 Hlook_digs]].
    { apply lookup_replicate in Hlook_digs. naive_solver. }
    apply list_lookup_singleton_Some in Hlook_digs as [Heq1 Hlook_digs].
    rewrite length_replicate in Heq0 Heq1.
    assert (ep = dig.(SigDig.Epoch)) as -> by word.
    rewrite lookup_insert. destruct dig. naive_solver.
  - subst new_digs. rewrite app_assoc last_snoc. naive_solver.
  - rewrite !length_app length_replicate. simpl. word.
  - iDestruct "Hcheck_memb" as
      (??) "(#His_label_memb & #His_commit_memb & #Hhas_merk_proof_memb)".
    iFrame "Hsl_val Hhas_merk_proof_memb Hhas_merk_proof_nonmemb".
    iExists (MembHide.MapVal <$> hist).
    rewrite Hlen_hist. iFrame "#". iApply (big_sepL_impl with "Hhist").
    iIntros "!> * _ H". iNamedSuffix "H" "_hist". iFrame "#".
  - iFrame "#".
Qed.

(* is_audit says we've audited up *to* (not including) bound. *)
Definition is_audit (cli_γ adtr_γ : gname) serv_vrf_pk (bound : w64) : iProp Σ :=
  ∃ adtr_st,
  "%Hlen_adtr" ∷ ⌜ length adtr_st = uint.nat bound ⌝ ∗
  "#Hlb_adtr" ∷ mono_list_lb_own adtr_γ adtr_st ∗
  "#Hdigs_adtr" ∷ ([∗ list] x ∈ adtr_st, is_dig (lower_adtr x.1) x.2) ∗
  "%Hinv_adtr" ∷ ⌜ adtr_inv (fst <$> adtr_st) ⌝ ∗
  "#Hmap_transf" ∷ (□ ∀ (ep : w64) m dig uid ver val,
    ("%Hlook_adtr" ∷ ⌜ adtr_st !! uint.nat ep = Some (m, dig) ⌝ ∗
    "#His_entry" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid ver val)
    -∗
    (∃ label,
    "#His_label" ∷ is_map_label serv_vrf_pk uid ver label ∗
    "%Hin_adtr" ∷ ⌜ m !! label = val ⌝)).

Definition auditEpoch_post adtr_pk seen_dig : iProp Σ :=
  □ ∀ adtr_γ,
  ("#His_pk" ∷ is_sig_pk adtr_pk (adtr_sigpred adtr_γ))
  -∗
  (∃ adtr_st m,
  "#Hlb_adtr" ∷ mono_list_lb_own adtr_γ adtr_st ∗
  "#Hdigs_adtr" ∷ ([∗ list] x ∈ adtr_st, is_dig (lower_adtr x.1) x.2) ∗
  "%Hlook_dig" ∷ ⌜ adtr_st !! uint.nat seen_dig.(SigDig.Epoch) =
    Some (m, seen_dig.(SigDig.Dig)) ⌝ ∗
  "%Hinv_adtr" ∷ ⌜ adtr_inv (fst <$> adtr_st) ⌝).

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
    "Hown_err" ∷ ClientErr.own ptr_err err serv_sig_pk ∗
    "Herr" ∷ if err.(ClientErr.Err) then True else auditEpoch_post adtr_pk seen_dig
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamedSuffix "Hown_seen_dig" "_seen".
  rewrite /auditEpoch. wp_pures.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_stdErr".
  wp_loadField.
  wp_apply (wp_callAdtrGet with "Hown_adtr_cli"). iIntros "* H". iNamed "H".
  wp_if_destruct.
  { iApply ("HΦ" $! _ (ClientErr.mk None _)). by iFrame "∗#". }
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
  { iApply ("HΦ" $! _ (ClientErr.mk None _)). by iFrame "∗#". }
  wp_apply (wp_CheckSigDig _ (SigDig.mk _ _ _) with "[#]"); [iFrame "#"|].
  iIntros (err1). iNamedSuffix 1 "_adtrSig". wp_if_destruct.
  { iApply ("HΦ" $! _ (ClientErr.mk None _)). by iFrame "∗#". }
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
    iApply ("HΦ" $! _ (ClientErr.mk (Some
      (Evid.mk (SigDig.mk seen_dig.(SigDig.Epoch)
        adtrInfo.(AdtrEpochInfo.Dig) adtrInfo.(AdtrEpochInfo.ServSig))
      seen_dig)) _)).
    by iFrame "∗#". }
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamedSuffix "H" "_err".
  iApply ("HΦ" $! _ (ClientErr.mk None _)).
  iFrame "∗#". iIntros (?) "!>". iNamed 1.
  iDestruct (is_sig_to_pred with "His_pk His_adtrSig") as "H".
  iNamed "H". apply PreSigDig.inj in Henc as <-. rewrite -Heqb2. iFrame "#%".
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

Lemma prefix_lookup_agree {A} l1 l2 i (x1 x2 : A) :
  l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 →
  l1 !! i = Some x1 →
  l2 !! i = Some x2 →
  x1 = x2.
Proof.
  intros Hpre Hlook1 Hlook2.
  destruct Hpre as [Hpre|Hpre].
  - opose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpre) as ?. by simplify_eq/=.
  - opose proof (prefix_lookup_Some _ _ _ _ Hlook2 Hpre) as ?. by simplify_eq/=.
Qed.

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
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv_sig_pk) ∗
    "Herr" ∷ if err.(ClientErr.Err) then True else
      ∀ adtr_γ,
      ("#His_pk" ∷ is_pk adtr_pk (adtr_sigpred adtr_γ))
      -∗
      ("#His_audit" ∷ is_audit c.(Client.γ) adtr_γ c.(Client.next_epoch))
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
    "Herr" ∷ ClientErr.own ptr_err0 err0 c.(Client.serv_sig_pk) ∗
    "Hptr_err0" ∷ ptr2_err0 ↦[ptrT] #ptr_err0 ∗
    if negb err0.(ClientErr.Err) then
      ∃ sd',
      "%Hdom" ∷ ⌜ dom sd_ptrs' = dom sd' ⌝ ∗
      "%Hsub" ∷ ⌜ sd' ⊆ sd ⌝ ∗
      "#Hpost" ∷ ([∗ map] x ∈ sd', auditEpoch_post adtr_pk x)
    else True)%I with "Hown_sd_map [$Hown_cli_adtr $Hptr_err0 Herr0]").
  { iDestruct (struct_fields_split with "Herr0") as "H". iNamed "H".
    iExists (ClientErr.mk None false). iFrame. iExists ∅.
    iSplit; [done|]. iSplit. { iPureIntro. by eapply map_empty_subseteq. }
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
      rewrite /ClientErr.own Heqb. by iFrame "∗#".
    - iApply "HΦ". iExists ptr_err0, err0.
      destruct err0.(ClientErr.Err) eqn:Heq_err0.
      + rewrite /ClientErr.own Heq_err0. by iFrame "∗#".
      + rewrite /ClientErr.own Heq_err0. iFrame.
        iNamedSuffix "Hpre" "_pre". iExists (<[k:=x2]>sd').
        iIntros "!>". iSplit. { iPureIntro. set_solver. }
        iSplit. { iPureIntro. by apply insert_subseteq_l. }
        iApply big_sepM_insert_2; iFrame "#". }
  iIntros "[Hown_sd_maps Hpost]". iNamed "Hpost". iClear "Hown_cli_adtr".
  iDestruct (mono_list_lb_own_get with "Hown_digs") as "#His_digs".
  wp_load. iApply "HΦ". iFrame "∗#%".
  destruct err0.(ClientErr.Err); [done|].
  iIntros "!>". iIntros (?). iNamed 1. iNamed "Hpost".
  iDestruct (big_sepM2_dom with "Hown_sd") as %Hdom1.
  opose proof (map_subset_dom_eq _ _ _ _ _ Hsub) as ->.
  { by rewrite -Hdom -Hdom1. }
  clear Hdom Hdom1 Hsub.

  (* process last ep to fill is_audit adtr maps. *)
  destruct (last digs) eqn:Hlast_dig; rewrite last_lookup in Hlast_dig.
  2: { exfalso. rewrite lookup_ge_None in Hlast_dig. word. }
  opose proof (Hlast_digs _ _) as [??]; [done|]. simplify_eq/=.
  rewrite Hlen_digs in Hlast_dig.
  replace (pred (uint.nat c.(Client.next_epoch))) with
    (Z.to_nat (uint.Z c.(Client.next_epoch) - 1%Z)) in Hlast_dig; [|word].
  pose proof (Hagree_digs_sd _ _ Hlast_dig) as [? Hlook_sd].
  iDestruct (big_sepM_lookup with "Hpost") as "H"; [exact Hlook_sd|].
  iSpecialize ("H" with "His_pk"). iNamed "H". simpl in *.

  iExists (take (uint.nat c.(Client.next_epoch)) adtr_st).
  iSplit.
  { iPureIntro. apply lookup_lt_Some in Hlook_dig.
    rewrite length_take_le; [done|word]. }
  iSplit. { iApply (mono_list_lb_own_le with "Hlb_adtr"). apply prefix_take. }
  iSplit. { iApply (big_sepL_take with "Hdigs_adtr"). }
  iSplit.
  { iPureIntro. rewrite fmap_take. refine (adtr_inv_prefix _ _ Hinv_adtr).
    apply prefix_take. }
  iClear (Hlook_sd Hlook_dig Hinv_adtr) "Hdigs_adtr".
  iRename "Hlb_adtr" into "Hlb_adtr0".

  (* process the ep in the wand precond. *)
  iIntros "!> *". iNamed 1. iNamed "His_entry". iFrame "His_label".
  iDestruct (mono_list_lb_idx_lookup with "His_digs His_dig") as %Hlook_digs.
  { apply lookup_lt_Some in Hlook_adtr.
    rewrite length_take in Hlook_adtr. word. }
  pose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd].
  iDestruct (big_sepM_lookup with "Hpost") as "H"; [exact Hlook_sd|].
  iSpecialize ("H" with "His_pk"). iNamed "H". simpl in *.
  rewrite w64_to_nat_id in Hlook_dig.
  iDestruct (big_sepL_lookup with "Hdigs_adtr") as "Hmerk_dig"; [exact Hlook_dig|].
  iDestruct (is_merkle_entry_with_map with "Hhas_merk_proof Hmerk_dig") as %Hlook_final.
  iDestruct (mono_list_lb_valid with "Hlb_adtr0 Hlb_adtr") as %Hpref.
  apply lookup_take_Some in Hlook_adtr as [Hlook_adtr _].
  opose proof (prefix_lookup_agree _ _ _ _ _ Hpref Hlook_adtr Hlook_dig) as ?.
  simplify_eq/=.
  rewrite lookup_fmap in Hlook_final.
  opose proof ((option_fmap_eq_inj _ _) _ _ Hlook_final) as ?; [|done].
  { intros [??][??] Hinj.
    opose proof (MapValPre.inj _ _ Hinj) as ?. naive_solver. }
Qed.

Lemma wp_newClient (uid servAddr : w64) sl_servSigPk servSigPk (servVrfPk : loc) :
  {{{
    "#Hsl_servSigPk" ∷ own_slice_small sl_servSigPk byteT DfracDiscarded servSigPk
  }}}
  newClient #uid #servAddr (slice_val sl_servSigPk) #servVrfPk
  {{{
    ptr_cli cli_γ r1 r2, RET #ptr_cli;
    "Hown_cli" ∷ Client.own ptr_cli (Client.mk cli_γ uid (W64 0) (W64 0) r1 servSigPk r2)
  }}}.
Proof. Admitted.

End wps.

Section derived.
Context `{!heapGS Σ, !pavG Σ}.

Lemma get_audit_msv cli_γ uid ep lat adtr_γ aud_ep :
  uint.Z ep < uint.Z aud_ep →
  ("#His_key" ∷ is_get_post cli_γ uid ep lat ∗
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
