From Perennial.program_proof.pav Require Import prelude.
From Goose.github_com.mit_pdos.pav Require Import kt.

From Perennial.program_proof.pav Require Import
  advrpc auditor core classes cryptoffi evidence logical_audit
  merkle rpc serde server.
From Perennial.program_proof Require Import std_proof.
From Perennial.Helpers Require Import Map.

Module Client.
Record t :=
  mk {
    γ: gname;
    uid: uid_ty;
    next_ver: ver_ty;
    next_epoch: epoch_ty;
    serv: Server.t;
    serv_is_good: bool;
  }.
Global Instance eta : Settable _ :=
  settable! mk <γ; uid; next_ver; next_epoch; serv; serv_is_good>.

Section defs.
Context `{!heapGS Σ, !pavG Σ}.

Definition own (ptr : loc) (obj : t) : iProp Σ :=
  ∃ digs ptr_sd sd_refs sd ptr_serv_cli sl_serv_sig_pk ptr_vrf_pk serv_addr,

  (* seenDigs (sd). *)
  "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
  "#Hptr_sd" ∷ ptr ↦[Client :: "seenDigs"]□ #ptr_sd ∗
  "#Hown_sd" ∷ ([∗ map] l;x ∈ sd_refs;sd, SigDig.own l x DfracDiscarded) ∗
  "#His_sd" ∷ ([∗ map] ep ↦ x ∈ sd,
    "%Heq_ep" ∷ ⌜ ep = x.(SigDig.Epoch) ⌝ ∗
    "#His_sigdig" ∷ is_SigDig x obj.(serv).(Server.sig_pk)) ∗

  (* uid, next_ver, next_epoch. *)
  "#Hptr_uid" ∷ ptr ↦[Client :: "uid"]□ #obj.(uid) ∗
  "Hptr_nextVer" ∷ ptr ↦[Client :: "nextVer"] #obj.(next_ver) ∗
  "Hptr_nextEpoch" ∷ ptr ↦[Client :: "nextEpoch"] #obj.(next_epoch) ∗

  (* server info. *)
  "Huid" ∷ (if negb obj.(serv_is_good) then True else
    obj.(uid) ↪[obj.(serv).(Server.γvers)] obj.(next_ver)) ∗
  (* "epoch increasing" req comes from viewing client consistency
  as having a forever-increasing (by epoch) history of its own key. *)
  "#Hlb_serv_ep" ∷ (if negb obj.(serv_is_good) then True else
    mono_nat_lb_own obj.(serv).(Server.γepoch) (uint.nat obj.(next_epoch))) ∗
  "Hown_servCli" ∷ advrpc.own_Client ptr_serv_cli serv_addr obj.(serv_is_good) ∗
  "#Hserv_sig_pk" ∷ (if negb obj.(serv_is_good) then True else
    is_sig_pk obj.(serv).(Server.sig_pk) (sigpred obj.(serv).(Server.γhist))) ∗
  "#Hptr_servCli" ∷ ptr ↦[Client :: "servCli"]□ #ptr_serv_cli ∗
  "#Hptr_servSigPk" ∷ ptr ↦[Client :: "servSigPk"]□ (slice_val sl_serv_sig_pk) ∗
  "#Hsl_servSigPk" ∷ own_slice_small sl_serv_sig_pk byteT
    DfracDiscarded obj.(serv).(Server.sig_pk) ∗
  "#Hserv_vrf_pk" ∷ is_vrf_pk ptr_vrf_pk obj.(serv).(Server.vrf_pk) ∗
  "#Hptr_servVrfPk" ∷ ptr ↦[Client :: "servVrfPk"]□ #ptr_vrf_pk ∗

  (* digs ghost state. *)
  "Hown_digs" ∷ mono_list_auth_own obj.(γ) 1 digs ∗
  "%Hagree_digs_sd" ∷ ⌜ ∀ (ep : w64) dig,
    digs !! (uint.nat ep) = Some (Some dig) →
    ∃ sig, sd !! ep = Some (SigDig.mk ep dig sig) ⌝ ∗
  (* for Get / SelfMon, might get back last seen epoch.
  we can't role back ghost state, so we must know that the last epoch
  actually had a dig and was physically checked for equality. *)
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
    "#Hown_evid" ∷ Evid.own ptr_evid e DfracDiscarded ∗
    "#His_evid" ∷ is_Evid e pk
  | None => True
  end.
End defs.
End ClientErr.

Section proof.
Context `{!heapGS Σ, !pavG Σ}.

(* Defs. *)

Definition is_cli_entry cli_γ serv_vrf_pk (ep : w64) uid ver val : iProp Σ :=
  ∃ dig label,
  "#Hlook_dig" ∷ mono_list_idx_own cli_γ (uint.nat ep) (Some dig) ∗
  "#Hvrf_out" ∷ is_vrf_out serv_vrf_pk (enc_label_pre uid ver) label ∗
  "#Hmerk_entry" ∷ is_merkle_entry label val dig.

Definition is_put_post cli_γ serv_vrf_pk uid ver ep pk : iProp Σ :=
  ∃ commit enc,
  "#Hcommit" ∷ is_commit pk commit ∗
  "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk ep commit) ⌝ ∗
  "#His_lat" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid ver (Some enc) ∗
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (word.add ver (W64 1)) None.

Definition is_selfmon_post cli_γ serv_vrf_pk uid ver (ep : w64) : iProp Σ :=
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid ver None.

Definition is_get_post_Some cli_γ serv_vrf_pk uid (ep : w64) pk : iProp Σ :=
  ∃ hist ep' commit enc,
  "#Hhist" ∷ ([∗ list] ver ↦ val ∈ hist,
    is_cli_entry cli_γ serv_vrf_pk ep uid ver (Some val)) ∗
  "#Hcommit" ∷ is_commit pk commit ∗
  "%Henc" ∷ ⌜ MapValPre.encodes enc (MapValPre.mk ep' commit) ⌝ ∗
  "#His_lat" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (W64 $ length hist) (Some enc) ∗
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (word.add (length hist) (W64 1)) None.

Definition is_get_post_None cli_γ serv_vrf_pk uid (ep : w64) : iProp Σ :=
  "#His_bound" ∷ is_cli_entry cli_γ serv_vrf_pk ep uid (W64 0) None.

(* WPs. *)

Lemma wp_NewClient uid (serv_addr : w64) sl_serv_sig_pk sl_serv_vrf_pk serv serv_is_good :
  {{{
    "Huid" ∷ (if negb serv_is_good then True else uid ↪[serv.(Server.γvers)] (W64 0)) ∗
    "#Hsl_serv_sig_pk" ∷ own_slice_small sl_serv_sig_pk byteT DfracDiscarded serv.(Server.sig_pk) ∗
    "#Hsl_serv_vrf_pk" ∷ own_slice_small sl_serv_vrf_pk byteT DfracDiscarded serv.(Server.vrf_pk) ∗
    "#His_good" ∷ (if negb serv_is_good then True else
      is_sig_pk serv.(Server.sig_pk) (sigpred serv.(Server.γhist)))
  }}}
  NewClient #uid #serv_addr (slice_val sl_serv_sig_pk) (slice_val sl_serv_vrf_pk)
  {{{
    ptr_c γ, RET #ptr_c;
    "Hown_cli" ∷ Client.own ptr_c
      (Client.mk γ uid (W64 0) (W64 0) serv serv_is_good)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply (wp_Dial _ serv_is_good). iIntros "*". iNamed 1.
  wp_apply (wp_VrfPublicKeyDecode with "[$Hsl_serv_vrf_pk]").
  iClear "Hsl_serv_vrf_pk". iIntros "*". iNamed 1.
  wp_apply wp_NewMap. iIntros "* Hown_sd_refs". wp_apply wp_fupd.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iMod (struct_field_pointsto_persist with "uid") as "#uid".
  iMod (struct_field_pointsto_persist with "servCli") as "#servCli".
  iMod (struct_field_pointsto_persist with "servSigPk") as "#servSigPk".
  iMod (struct_field_pointsto_persist with "servVrfPk") as "#servVrfPk".
  iMod (struct_field_pointsto_persist with "seenDigs") as "#seenDigs".
  iMod (mono_list_own_alloc []) as (?) "[Hown_digs _]".
  iMod (mono_nat_lb_own_0 serv.(Server.γepoch)) as "#Hep".
  iApply "HΦ". iFrame "∗#". iExists ∅. iModIntro.
  simpl. repeat (iSplit; [naive_solver|]).
  iSplit; [by case_match|].
  by repeat (iSplit; [naive_solver|]).
Qed.

Lemma wp_checkDig sl_sig_pk (sig_pk : list w8) ptr_sd (sd_refs : gmap w64 loc) sd ptr_dig dig :
  let wish := (
    "#His_dig" ∷ is_SigDig dig sig_pk ∗
    "%Hnoof_ep" ∷ ⌜ uint.Z (word.add dig.(SigDig.Epoch) (W64 1)) =
      (uint.Z dig.(SigDig.Epoch) + 1)%Z ⌝ ∗
    "%Heq_old" ∷ ⌜ ∀ old, sd !! dig.(SigDig.Epoch) = Some old →
      dig.(SigDig.Dig) = old.(SigDig.Dig) ⌝)%I in
  {{{
    "#Hsl_sig_pk" ∷ own_slice_small sl_sig_pk byteT DfracDiscarded sig_pk ∗
    "#Hown_sd" ∷ ([∗ map] l;x ∈ sd_refs;sd, SigDig.own l x DfracDiscarded) ∗
    "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
    "#His_sd" ∷ ([∗ map] ep ↦ x ∈ sd,
      "%Heq_ep" ∷ ⌜ ep = x.(SigDig.Epoch) ⌝ ∗
      "#His_sigdig" ∷ is_SigDig x sig_pk) ∗
    "#Hsigdig" ∷ SigDig.own ptr_dig dig DfracDiscarded
  }}}
  checkDig (slice_val sl_sig_pk) #ptr_sd #ptr_dig
  {{{
    err ptr_err, RET #ptr_err;
    "Hown_sd_refs" ∷ own_map ptr_sd (DfracOwn 1) sd_refs ∗
    "Hown_err" ∷ ClientErr.own ptr_err err sig_pk ∗
    "Hgenie" ∷ (⌜ err.(ClientErr.Err) = false ⌝ ∗-∗ wish)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) sig_pk) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }
  wp_apply (wp_CheckSigDig with "[$Hsigdig $Hsl_sig_pk]").
  iIntros "*". iNamed 1.
  wp_if_destruct.
  { iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iDestruct "Hgenie" as "[_ Hgenie]".
    by iDestruct ("Hgenie" with "His_dig") as %?. }
  iDestruct "Hgenie" as "[H _]".
  iDestruct ("H" with "[//]") as "#His_sigdig".
  iNamed "Hsigdig".
  wp_loadField. wp_apply wp_SumNoOverflow. wp_if_destruct.
  { iApply "HΦ". iFrame. iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. word. }
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
    - wp_apply wp_allocStruct; [val_ty|]. iIntros "* H". iPersist "H".
      iDestruct (struct_fields_split with "H") as "{H} H". iNamed "H".
      wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
      iDestruct (struct_fields_split with "H") as "H". iNamed "H".
      iApply ("HΦ" $! (ClientErr.mk (Some (Evid.mk dig x)) true)).
      iFrame "∗#". simpl. iSplit; [done|]. iSplit. { by iIntros (?). }
      iNamed 1. naive_solver.
    - wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
      iDestruct (struct_fields_split with "H") as "H". iNamed "H".
      iApply ("HΦ" $! (ClientErr.mk None false)).
      iFrame "∗#%". iSplit; [|naive_solver]. iIntros "_".
      iPureIntro. naive_solver. }
  apply map_get_false in Hlook_sd_refs as [Hlook_sd_refs _].
  iDestruct (big_sepM2_lookup_l_none with "Hown_sd") as %Hlook_sd;
    [exact Hlook_sd_refs|].
  iClear "Hown_std_err". wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  iApply ("HΦ" $! (ClientErr.mk None false)).
  iFrame "∗#%". iSplit; [|naive_solver]. iIntros (_).
  iPureIntro. naive_solver.
Qed.

Lemma wp_checkLabel ptr_vrf_pk vrf_pk sl_proof d0 uid ver (proof : list w8) :
  let wish := (λ label,
    "#Hvrf_proof" ∷ is_vrf_proof vrf_pk (enc_label_pre uid ver) proof ∗
    "#Hvrf_out" ∷ is_vrf_out vrf_pk (enc_label_pre uid ver) label
  )%I in
  {{{
    "#Hvrf_pk" ∷ is_vrf_pk ptr_vrf_pk vrf_pk ∗
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d0 proof
  }}}
  checkLabel #ptr_vrf_pk #uid #ver (slice_val sl_proof)
  {{{
    sl_label (label : list w8) (err : bool), RET (slice_val sl_label, #err);
    "Hsl_proof" ∷ own_slice_small sl_proof byteT d0 proof ∗
    "Hsl_label" ∷ own_slice_small sl_label byteT (DfracOwn 1) label ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ ∃ label', wish label') ∗
    "Herr" ∷ (∀ label', wish label' -∗ "->" ∷ ⌜ label = label' ⌝)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_allocStruct; [val_ty|]. iIntros "* H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_apply wp_NewSliceWithCap; [word|].
  iIntros "* Hsl_enc".
  wp_apply (MapLabelPre.wp_enc (MapLabelPre.mk _ _) with "[$Hsl_enc $Uid $Ver]").
  iIntros "*". iNamed 1. simpl.
  iDestruct (own_slice_to_small with "Hsl_b") as "Hsl_b".
  wp_apply (wp_VrfPublicKey__Verify with "[$Hvrf_pk $Hsl_b $Hsl_proof]").
  iIntros "*". iNamed 1.
  replace (uint.nat (W64 0)) with (0%nat); [|word]. simpl.
  rewrite /MapLabelPre.encodes in Henc. subst.
  iApply "HΦ". iFrame. destruct err.
  - iDestruct "Hgenie" as "[_ Hgenie]".
    (* give genie to one side and err to other. *)
    iSplitL "Hgenie".
    + iSplit. { by iIntros (?). } iNamed 1. by iApply "Hgenie".
    + iIntros (?). iNamed 1.
      iDestruct ("Herr" with "Hvrf_proof") as "#Hvrf_out0".
      by iApply is_vrf_out_det.
  - iDestruct "Hgenie" as "[Hgenie _]".
    iDestruct ("Hgenie" with "[//]") as "#Hvrf_proof".
    iDestruct ("Herr" with "Hvrf_proof") as "#Hvrf_out".
    iSplitL.
    + iSplit; [|naive_solver]. iIntros (_). iFrame "#".
    + iIntros (?). iNamedSuffix 1 "0". by iApply is_vrf_out_det.
Qed.

Lemma wp_checkMemb ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_memb memb d0 :
  {{{
    "#Hvrf_pk" ∷ is_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hown_memb" ∷ Memb.own ptr_memb memb d0
  }}}
  checkMemb #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_memb
  {{{
    (err : bool), RET #err;
    "Hown_memb" ∷ Memb.own ptr_memb memb d0 ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗
      ∃ label commit, wish_checkMemb vrf_pk uid ver dig memb label commit)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hown_memb". wp_loadField.
  wp_apply (wp_checkLabel with "[$Hvrf_pk $Hsl_labelP]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { iApply "HΦ". iFrame "∗#". iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie". iFrame "#". }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[$]") as "H". iNamed "H".
  do 2 wp_loadField.
  wp_apply (wp_compMapVal with "[$Hpk_open]"). iIntros "*". iNamed 1.
  wp_loadField.
  wp_apply (wp_Verify with "[$Hsl_label $Hsl_map_val]").
  { iFrame "#". }
  iIntros (err0) "{Hsl_dig}". iNamed 1.
  iApply "HΦ". iFrame "∗#". destruct err0.
  - iSplit. { by iIntros (?). }
    iNamedSuffix 1 "0". iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie".
    iDestruct (is_vrf_out_det with "Hvrf_out Hvrf_out0") as %->.
    by iDestruct (is_hash_det with "Hcommit Hcommit0") as %->.
  - iSplit; [|naive_solver]. iIntros (_).
    iDestruct "Hgenie" as "[Hgenie _]".
    iDestruct ("Hgenie" with "[//]") as "#Hmerk".
    iFrame "∗#".
Qed.

Lemma wp_checkMembHide ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_memb_hide memb_hide d0 :
  {{{
    "#Hvrf_pk" ∷ is_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hmemb_hide" ∷ MembHide.own ptr_memb_hide memb_hide d0
  }}}
  checkMembHide #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_memb_hide
  {{{
    (err : bool), RET #err;
    "Hmemb_hide" ∷ MembHide.own ptr_memb_hide memb_hide d0 ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗
      ∃ label, wish_checkMembHide vrf_pk uid ver dig memb_hide label)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hmemb_hide". wp_loadField.
  wp_apply (wp_checkLabel with "[$Hvrf_pk $Hsl_labelP]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { iApply "HΦ". iFrame "∗#". iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie". iFrame "#". }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[$]") as "H". iNamed "H".
  do 2 wp_loadField.
  wp_apply (wp_Verify with "[$Hsl_label $Hsl_map_val]").
  { iFrame "#". }
  iIntros (err0) "{Hsl_dig}". iNamed 1.
  iApply "HΦ". iFrame "∗#". destruct err0.
  - iSplit. { by iIntros (?). }
    iNamedSuffix 1 "0". iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie".
    by iDestruct (is_vrf_out_det with "Hvrf_out Hvrf_out0") as %->.
  - iSplit; [|naive_solver]. iIntros (_).
    iDestruct "Hgenie" as "[Hgenie _]".
    iDestruct ("Hgenie" with "[//]") as "#Hmerk".
    iFrame "∗#".
Qed.

Lemma wp_checkHist ptr_vrf_pk vrf_pk (uid : w64) sl_dig (dig : list w8) sl_hist (histref : list loc) hist d0 :
  let wish := (
    "#Hwish_hist" ∷ ([∗ list] ver ↦ x ∈ hist,
      ∃ label,
      wish_checkMembHide vrf_pk uid (W64 ver) dig x label))%I in
  {{{
    "#Hvrf_pk" ∷ is_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "#Hsl_hist" ∷ own_slice_small sl_hist ptrT DfracDiscarded histref ∗
    "Hown_hist" ∷ ([∗ list] ptr_memb_hide;memb_hide ∈ histref;hist,
      MembHide.own ptr_memb_hide memb_hide d0)
  }}}
  checkHist #ptr_vrf_pk #uid (slice_val sl_dig) (slice_val sl_hist)
  {{{
    (err : bool), RET #err;
    "Hown_hist" ∷ ([∗ list] ptr_memb_hide;memb_hide ∈ histref;hist,
      MembHide.own ptr_memb_hide memb_hide d0) ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ wish)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  wp_apply wp_ref_of_zero; [done|]. iIntros (ptr_err0) "Hptr_err0".
  wp_apply (wp_forSlice
    (λ i,
    ∃ (err0 : bool),
    "Hown_hist" ∷ ([∗ list] ptr_memb_hide;memb_hide ∈ histref;hist,
      MembHide.own ptr_memb_hide memb_hide d0) ∗
    "Hptr_err0" ∷ ptr_err0 ↦[boolT] #err0 ∗
    "Hloop_err" ∷ (⌜ err0 = false ⌝ ∗-∗
      "#Hwish_hist" ∷
        ([∗ list] ver ↦ x ∈ take (uint.nat i) hist,
        ∃ label,
        wish_checkMembHide vrf_pk uid (W64 ver) dig x label)))%I
    with "[] [$Hown_hist $Hptr_err0 $Hsl_hist]").
  { clear. iIntros "*". iIntros (Φ) "!> (H&%&%Hlook_histref) HΦ". iNamed "H".
    iDestruct (big_sepL2_lookup_1_some with "Hown_hist") as %[? Hlook_hist];
      [exact Hlook_histref|].
    iDestruct (big_sepL2_lookup_acc with "Hown_hist") as "[Hown_memb_hide Hacc]";
      [exact Hlook_histref|exact Hlook_hist|].
    wp_apply (wp_checkMembHide with "[$Hvrf_pk $Hsl_dig $Hown_memb_hide]").
    iIntros "*". iNamed 1.
    iDestruct ("Hacc" with "Hmemb_hide") as "Hown_hist". wp_if_destruct.
    { wp_store. iApply "HΦ". iFrame "∗#".
      iIntros "!>". iSplit. { by iIntros (?). }
      iNamed 1. iDestruct "Hgenie" as "[_ Hgenie]". iApply "Hgenie".
      iDestruct (big_sepL_lookup_acc _ _ (uint.nat i) x0 with "Hwish_hist") as "[Hcontr _]".
      { rewrite lookup_take; [done|word]. }
      by rewrite w64_to_nat_id. }
    iDestruct "Hgenie" as "[Hgenie _]".
    iDestruct ("Hgenie" with "[//]") as "H".
    iDestruct "H" as (?) "#Hmerk".
    replace (uint.nat (word.add i (W64 1))) with (S (uint.nat i)) by word.
    rewrite (take_S_r _ _ x0); [|done].
    iApply "HΦ". iFrame. iIntros "!>". destruct err0.
    - iSplit. { by iIntros (?). }
      iNamed 1. iDestruct "Hloop_err" as "[_ Hcontr]". iApply "Hcontr".
      iDestruct (big_sepL_snoc with "Hwish_hist") as "[$ _]".
    - iSplit; [|naive_solver]. iIntros (_).
      iDestruct "Hloop_err" as "[Hloop_err _]".
      iDestruct ("Hloop_err" with "[//]") as "H". iNamed "H".
      iApply big_sepL_snoc.
      replace (W64 (length _)) with (i).
      2: { rewrite length_take. apply lookup_lt_Some in Hlook_hist. word. }
      iFrame "#". }
  { naive_solver. }
  iIntros "(H&_)". iNamed "H". wp_load.
  iDestruct (big_sepL2_length with "Hown_hist") as %?.
  iDestruct (own_slice_small_sz with "Hsl_hist") as %?.
  rewrite take_ge; [|lia].
  iApply "HΦ". by iFrame.
Qed.

Lemma wp_checkNonMemb ptr_vrf_pk vrf_pk (uid ver : w64) sl_dig (dig : list w8) ptr_non_memb non_memb d0 :
  {{{
    "#Hvrf_pk" ∷ is_vrf_pk ptr_vrf_pk vrf_pk ∗
    "#Hsl_dig" ∷ own_slice_small sl_dig byteT DfracDiscarded dig ∗
    "Hown_non_memb" ∷ NonMemb.own ptr_non_memb non_memb d0
  }}}
  checkNonMemb #ptr_vrf_pk #uid #ver (slice_val sl_dig) #ptr_non_memb
  {{{
    (err : bool), RET #err;
    "Hown_non_memb" ∷ NonMemb.own ptr_non_memb non_memb d0 ∗
    "Hgenie" ∷ (⌜ err = false ⌝ ∗-∗ wish_checkNonMemb vrf_pk uid ver dig non_memb)
  }}}.
Proof.
  simpl. iIntros (Φ) "H HΦ". iNamed "H". wp_rec.
  iNamed "Hown_non_memb". wp_loadField.
  wp_apply (wp_checkLabel with "[$Hvrf_pk $Hsl_labelP]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { iApply "HΦ". iFrame "∗#". iIntros "!>". iSplit. { by iIntros (?). }
    iNamed 1. iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie". iFrame "#". }
  iDestruct "Hgenie" as "[Hgenie _]".
  iDestruct ("Hgenie" with "[//]") as "H". iNamed "H".
  iDestruct ("Herr" with "[$]") as "H". iNamed "H".
  wp_loadField.
  wp_apply (wp_Verify _ Slice.nil with "[$Hsl_label]").
  { iFrame "#".
    iApply own_slice_to_small. iApply (own_slice_zero _ DfracDiscarded). }
  iIntros (err0) "{Hsl_dig}". iNamed 1.
  iApply "HΦ". iFrame "∗#". destruct err0.
  - iSplit. { by iIntros (?). }
    iNamedSuffix 1 "0". iDestruct "Hgenie" as "[_ Hgenie]".
    iApply "Hgenie".
    by iDestruct (is_vrf_out_det with "Hvrf_out Hvrf_out0") as %->.
  - iSplit; [|naive_solver]. iIntros (_).
    iDestruct "Hgenie" as "[Hgenie _]".
    iDestruct ("Hgenie" with "[//]") as "#Hmerk".
    iFrame "∗#".
Qed.

Lemma is_sigdig_agree sd0 sd1 pk γ :
  sd0.(SigDig.Epoch) = sd1.(SigDig.Epoch) →
  is_sig_pk pk (sigpred γ) -∗
  is_SigDig sd0 pk -∗
  is_SigDig sd1 pk -∗
  ⌜ sd0.(SigDig.Dig) = sd1.(SigDig.Dig) ⌝.
Proof.
  iIntros (Heq) "#Hpk". iNamedSuffix 1 "0". iNamedSuffix 1 "1".
  iDestruct (is_sig_to_pred with "Hpk Hsig0") as "H". iNamedSuffix "H" "0".
  iDestruct (is_sig_to_pred with "Hpk Hsig1") as "H". iNamedSuffix "H" "1".
  (* unify with sigdig existentially hidden by sigpred. *)
  opose proof (PreSigDig.inj _ _ _ _ [] [] _ Henc1 Henc3); eauto.
  opose proof (PreSigDig.inj _ _ _ _ [] [] _ Henc0 Henc2); eauto.
  intuition. simplify_eq/=.
  iDestruct (mono_list_idx_own_get with "Hlb0") as "Hidx0"; [done|].
  iDestruct (mono_list_idx_own_get with "Hlb1") as "Hidx1"; [done|].
  rewrite Heq.
  iDestruct (mono_list_idx_agree with "Hidx0 Hidx1") as %?.
  naive_solver.
Qed.

Lemma mk_is_sigdig l sd d0 pk :
  SigDig.own l sd d0 -∗
  is_sig pk
    (PreSigDig.encodesF $ PreSigDig.mk sd.(SigDig.Epoch) sd.(SigDig.Dig))
    sd.(SigDig.Sig) -∗
  is_SigDig sd pk.
Proof.
  iNamed 1. iIntros "#Hsig". iFrame "#".
  iSplit; [|done].
  iDestruct (own_slice_small_sz with "Hsl_Dig") as %?.
  simpl. word.
Qed.

Lemma wp_Client__Put ptr_c c sl_pk d0 (pk : list w8) :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk
  }}}
  Client__Put #ptr_c (slice_val sl_pk)
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    (* TODO: prove that with ClientErr, could not have is_sig_pk. *)
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv).(Server.sig_pk) ∗
    (* can only prove genie one way. can't prove serv good w/ err = false. *)
    "%Hgenie" ∷ ⌜ c.(Client.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hown_cli" ∷ Client.own ptr_c c
      else
        let new_c := set Client.next_ver (λ x, (word.add x (W64 1)))
          (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
        "Hown_cli" ∷ Client.own ptr_c new_c ∗
        "#His_put_post" ∷ is_put_post c.(Client.γ) c.(Client.serv).(Server.vrf_pk)
          c.(Client.uid) c.(Client.next_ver) ep pk ∗
        "%Hnoof_ver" ∷ ⌜ uint.Z (word.add c.(Client.next_ver) (W64 1)) =
          (uint.Z c.(Client.next_ver) + 1)%Z ⌝ ∗
        (* TODO: there's some weird scope issues forcing us to Z scope here. *)
        "%Hnoof_ep" ∷ ⌜ uint.Z new_c.(Client.next_epoch) = (uint.Z ep + 1)%Z ⌝ ∗
        "%Hlt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) < uint.Z new_c.(Client.next_epoch) ⌝)
  }}}.
Proof. Admitted. (*
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_cli". wp_rec.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv).(Server.sig_pk)) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }

  do 2 wp_loadField.
  wp_apply (wp_CallServPut with "[$Hown_servCli $Huid $Hsl_pk $Hlb_serv_ep]").
  iIntros "*". iNamed 1.
  (* TODO: wp_pures takes a long time for some reason. *)
  wp_pures. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [naive_solver|done]. }
  iNamed "Herr". do 2 wp_loadField.

  wp_apply (wp_checkDig with "[$Hsl_servSigPk $Hown_sd $Hown_sd_refs $His_sd $Hsigdig]").
  iIntros (err1) "*". iNamed 1.
  iNamedSuffix "Hown_err" "1". wp_loadField. wp_if_destruct.
  { iDestruct "Hgenie" as "[_ Hgenie]".
    wp_pures. iApply ("HΦ" $! (ClientErr.mk _ _)). iFrame "∗#%".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood".
    iDestruct (mk_is_sigdig with "Hsigdig Hsig") as "#His_sigdig".
    iDestruct ("Hgenie" with "[]") as %?; [|done].
    iFrame "#".
    iSplit; [word|].
    iIntros (? Hlook_sd).
    iDestruct (big_sepM_lookup with "His_sd") as "H"; [done|].
    iNamedSuffix "H" "0".
    iDestruct (is_sigdig_agree with "Hserv_sig_pk His_sigdig His_sigdig0")
      as %?; eauto. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iSpecialize ("Hgenie" with "[//]").
  iNamed "Hgenie".
  iClear "Hptr_evid1 Hptr_err1 Hevid1".

  iPoseProof "Hsigdig" as "H". iNamed "H".
  do 2 wp_loadField. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood". word. }

  do 4 wp_loadField.
  wp_apply (wp_checkMemb with "[$Hserv_vrf_pk $Hsl_Dig $Hlat]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    iDestruct "Hgenie" as "[_ Hgenie]".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood".
    by iDestruct ("Hgenie" with "[$Hwish_lat]") as %?. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iSpecialize ("Hgenie" with "[//]").
  iNamedSuffix "Hgenie" "_lat".

  iNamed "Hown_memb".
  do 2 wp_loadField. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [|done].
    by iNamed "Hgood". }
  move: Heqb3 => Heq_ep.

  iNamed "Hpk_open". do 2 wp_loadField.
  wp_apply (wp_BytesEqual with "[$Hsl_pk $Hsl_val]").
  iIntros "[Hsl_pk Hsl_val]". wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [|done].
    by iNamed "Hgood". }
  move: Heqb => Heq_pk.

  do 4 wp_loadField.
  wp_apply (wp_checkNonMemb with "[$Hserv_vrf_pk $Hsl_Dig $Hbound]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    iDestruct "Hgenie" as "[_ Hgenie]".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood".
    by iDestruct ("Hgenie" with "[$Hwish_bound]") as %?. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iSpecialize ("Hgenie" with "[//]").
  iNamedSuffix "Hgenie" "_bound".

  do 2 wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_sd_refs]").
  iIntros "Hown_sd_refs". wp_loadField. wp_storeField. wp_loadField.
  wp_apply wp_SumAssumeNoOverflow. iIntros "%Hnoof_ver".
  wp_storeField. wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_pures. iApply ("HΦ" $! (ClientErr.mk None false)).
  iDestruct (big_sepM2_insert_2
    (λ _ x y, SigDig.own x y DfracDiscarded) _ _ sigdig.(SigDig.Epoch)
    with "Hsigdig Hown_sd") as "Hnew_own_sd".
  iDestruct (big_sepM_insert_2 _ _ sigdig.(SigDig.Epoch)
    with "[] His_sd") as "Hnew_is_sd". { by iFrame "#". }
  iClear "Hown_sd His_sd Hsigdig His_dig".

  (* grow ghost digs. *)
  set (digs ++ (replicate (uint.nat sigdig.(SigDig.Epoch) - length digs) None) ++
    [Some sigdig.(SigDig.Dig)]) as new_digs.
  iMod (mono_list_auth_own_update new_digs with "Hown_digs") as "[Hown_digs #Hlb]".
  { by apply prefix_app_r. }
  iDestruct (mono_list_idx_own_get (uint.nat sigdig.(SigDig.Epoch)) with "Hlb") as "#Hlook_gdigs".
  { rewrite lookup_app_r; [|word].
    rewrite lookup_app_r; rewrite length_replicate; [|done].
    apply list_lookup_singleton_Some. split; [lia|done]. }

  iDestruct (wish_merkle_Verify_to_entry with "Hmerk_lat") as "Hentry_lat".
  iDestruct (wish_merkle_Verify_to_entry with "Hmerk_bound") as "Hentry_bound".
  iDestruct (is_hash_len with "Hcommit_lat") as %?.

  rewrite -Heq_ep. iFrame "∗#". iIntros "!>".
  repeat try iSplit; simpl in *; try word.

  2: { destruct lat, PkOpen. rewrite Heq_pk. iFrame "#".
    iPureIntro. split; [|done]. simpl. word. }

  (* get all the serv_is_good obligations together. *)
  iEval (rewrite sep_assoc). iSplitL.
  { destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood". iFrame "∗#". }

  iPureIntro. repeat try split.
  - intros ep ? Hlook_digs.
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[? Hlook_digs]].
    { rewrite lookup_insert_ne. 2: { apply lookup_lt_Some in Hlook_digs. word. }
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd]. naive_solver. }
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[Heq0 Hlook_digs]].
    { apply lookup_replicate in Hlook_digs. naive_solver. }
    apply list_lookup_singleton_Some in Hlook_digs as [Heq1 Hlook_digs].
    rewrite length_replicate in Heq0 Heq1.
    assert (ep = sigdig.(SigDig.Epoch)) as -> by word.
    rewrite lookup_insert. destruct sigdig. naive_solver.
  - subst new_digs. rewrite app_assoc last_snoc. naive_solver.
  - rewrite !length_app length_replicate. simpl. word.
Qed.
*)

Lemma wp_Client__SelfMon ptr_c c :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__SelfMon #ptr_c
  {{{
    err (ep : w64) ptr_err, RET (#ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv).(Server.sig_pk) ∗
    "%Hgenie" ∷ ⌜ c.(Client.serv_is_good) = true → err.(ClientErr.Err) = false ⌝ ∗

    "Herr" ∷ (if err.(ClientErr.Err)
      then
        "Hown_cli" ∷ Client.own ptr_c c
      else
        let new_c := (set Client.next_epoch (λ _, (word.add ep (W64 1))) c) in
        "Hown_cli" ∷ Client.own ptr_c new_c ∗
        "#His_selfmon_post" ∷ is_selfmon_post c.(Client.γ) c.(Client.serv).(Server.vrf_pk)
          c.(Client.uid) c.(Client.next_ver) ep ∗
        "%Hnoof_ep" ∷ ⌜ uint.Z new_c.(Client.next_epoch) = (uint.Z ep + 1)%Z ⌝ ∗
        "%Hlt_ep" ∷ ⌜ uint.Z c.(Client.next_epoch) ≤ uint.Z new_c.(Client.next_epoch) ⌝)
  }}}.
Proof.
  iIntros (Φ) "H HΦ". iNamed "H". iNamed "Hown_cli". wp_rec.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv).(Server.sig_pk)) with "[H]" as "Hown_std_err".
  { iDestruct (struct_fields_split with "H") as "H". iNamed "H". iFrame. }

  do 2 wp_loadField.
  wp_apply (wp_CallServSelfMon with "[$Hown_servCli $Huid $Hlb_serv_ep]").
  iIntros "*". iNamed 1.
  wp_pures. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [naive_solver|done]. }
  iNamed "Herr". do 2 wp_loadField.

  wp_apply (wp_checkDig with "[$Hsl_servSigPk $Hown_sd $Hown_sd_refs $His_sd $Hsigdig]").
  iIntros (err1) "*". iNamed 1.
  iNamedSuffix "Hown_err" "1". wp_loadField. wp_if_destruct.
  { iDestruct "Hgenie" as "[_ Hgenie]".
    wp_pures. iApply ("HΦ" $! (ClientErr.mk _ _)). iFrame "∗#%".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood".
    iDestruct (mk_is_sigdig with "Hsigdig Hsig") as "#His_sigdig".
    iDestruct ("Hgenie" with "[]") as %?; [|done].
    iFrame "#".
    iSplit; [word|].
    iIntros (? Hlook_sd).
    iDestruct (big_sepM_lookup with "His_sd") as "H"; [done|].
    iNamedSuffix "H" "0".
    iDestruct (is_sigdig_agree with "Hserv_sig_pk His_sigdig His_sigdig0")
      as %?; eauto. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iSpecialize ("Hgenie" with "[//]").
  iNamed "Hgenie".
  iClear "Hptr_evid1 Hptr_err1 Hevid1".

  iPoseProof "Hsigdig" as "H". iNamed "H".
  do 2 wp_loadField. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood". word. }

  do 4 wp_loadField.
  wp_apply (wp_checkNonMemb with "[$Hserv_vrf_pk $Hsl_Dig $Hbound]").
  iIntros "*". iNamed 1. wp_if_destruct.
  { wp_pures. iApply "HΦ". iFrame "∗#%∗".
    iDestruct "Hgenie" as "[_ Hgenie]".
    destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood".
    by iDestruct ("Hgenie" with "[$Hwish_bound]") as %?. }
  iDestruct "Hgenie" as "[Hgenie _]".
  iSpecialize ("Hgenie" with "[//]").
  iNamedSuffix "Hgenie" "_bound".

  do 2 wp_loadField.
  wp_apply (wp_MapInsert_to_val with "[$Hown_sd_refs]").
  iIntros "Hown_sd_refs". wp_loadField. wp_storeField. wp_loadField.
  wp_apply wp_allocStruct; [val_ty|]. iIntros (?) "H".
  iDestruct (struct_fields_split with "H") as "H". iNamed "H".
  wp_pures. iApply ("HΦ" $! (ClientErr.mk None false)).
  iDestruct (big_sepM2_insert_2
    (λ _ x y, SigDig.own x y DfracDiscarded) _ _ sigdig.(SigDig.Epoch)
    with "Hsigdig Hown_sd") as "Hnew_own_sd".
  iDestruct (big_sepM_insert_2 _ _ sigdig.(SigDig.Epoch)
    with "[] His_sd") as "Hnew_is_sd". { by iFrame "#". }
  iClear "Hown_sd His_sd Hsigdig His_dig".

  iDestruct (wish_merkle_Verify_to_entry with "Hmerk_bound") as "Hentry_bound".
  iFrame "Hown_sd_refs Hptr_nextVer Hown_cli Hptr_nextEpoch Hserv_vrf_pk Evid Err #".

  destruct (decide (uint.Z sigdig.(SigDig.Epoch) + 1 = Z.of_nat (length digs))).
  (* case 1: new dig equals end of old digs. *)
  { list_elem digs (pred $ length digs) as last_dig.
    rewrite -last_lookup in Hlast_dig_lookup.
    opose proof (Hlast_digs _ Hlast_dig_lookup) as [? ->].
    rewrite last_lookup in Hlast_dig_lookup.
    replace (pred (length digs)) with (uint.nat sigdig.(SigDig.Epoch)) in Hlast_dig_lookup; [|word].
    opose proof (Hagree_digs_sd _ _ Hlast_dig_lookup) as [? Hlook_sd].
    opose proof (Heq_old _ Hlook_sd) as Heq_dig. simplify_eq/=.

    iDestruct (mono_list_idx_own_get _ _ Hlast_dig_lookup with "[Hown_digs]") as "#Hlook_gdigs".
    { by iApply mono_list_lb_own_get. }
    iFrame "Hlook_gdigs Hown_digs %". iIntros "!>".

    iEval (rewrite -!sep_assoc sep_assoc). iSplitL.
    { destruct c.(Client.serv_is_good); [|done].
      iNamed "Hgood". iFrame "∗#". }
    repeat try iSplit; [|word..].
    iIntros (ep ? Hlook_digs) "!%".
    opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd2].
    destruct (decide (ep = sigdig.(SigDig.Epoch))) as [->|].
    + rewrite lookup_insert. destruct sigdig. naive_solver.
    + rewrite lookup_insert_ne; [naive_solver|done]. }

  (* case 2: new dig greater than old digs. update ghost state. *)
  assert (uint.Z sigdig.(SigDig.Epoch) >= Z.of_nat (length digs)); [word|].
  set (digs ++ (replicate (uint.nat sigdig.(SigDig.Epoch) - length digs) None) ++
    [Some sigdig.(SigDig.Dig)]) as new_digs.
  iMod (mono_list_auth_own_update new_digs with "Hown_digs") as "[Hown_digs #Hlb]".
  { by apply prefix_app_r. }
  iDestruct (mono_list_idx_own_get (uint.nat sigdig.(SigDig.Epoch)) with "Hlb") as "#Hlook_gdigs".
  { rewrite lookup_app_r; [|word].
    rewrite lookup_app_r; rewrite length_replicate; [|done].
    apply list_lookup_singleton_Some. split; [lia|done]. }
  iFrame "∗#". iIntros "!>". iSplit; [done|]. simpl.

  iEval (rewrite -!sep_assoc sep_assoc). iSplitL.
  { destruct c.(Client.serv_is_good); [|done].
    iNamed "Hgood". iFrame "∗#". }

  iIntros "!%". repeat try split; try word.
  - intros ep ? Hlook_digs.
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[? Hlook_digs]].
    { rewrite lookup_insert_ne. 2: { apply lookup_lt_Some in Hlook_digs. word. }
      opose proof (Hagree_digs_sd _ _ Hlook_digs) as [? Hlook_sd]. naive_solver. }
    apply lookup_app_Some in Hlook_digs as [Hlook_digs|[Heq0 Hlook_digs]].
    { apply lookup_replicate in Hlook_digs. naive_solver. }
    apply list_lookup_singleton_Some in Hlook_digs as [Heq1 Hlook_digs].
    rewrite length_replicate in Heq0 Heq1.
    assert (ep = sigdig.(SigDig.Epoch)) as -> by word.
    rewrite lookup_insert. destruct sigdig. naive_solver.
  - subst new_digs. rewrite app_assoc last_snoc. naive_solver.
  - rewrite !length_app length_replicate. simpl. word.
Qed.

Lemma wp_Client__Get ptr_c c uid :
  {{{
    "Hown_cli" ∷ Client.own ptr_c c
  }}}
  Client__Get #ptr_c #uid
  {{{
    err (is_reg : bool) sl_pk (ep : w64) ptr_err,
    RET (#is_reg, slice_val sl_pk, #ep, #ptr_err);
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv).(Server.sig_pk) ∗
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
  iAssert (ClientErr.own _ (ClientErr.mk None _) c.(Client.serv).(Server.sig_pk)) with "[H]" as "Hown_std_err".
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
  iDestruct (big_sepM_insert_2 _ _ dig.(SigDig.Epoch)
    with "[His_dig] His_sd") as "Hnew_is_sd". { by iFrame "His_dig". }
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
  wp_apply (wp_CallAdtrGet with "Hown_adtr_cli"). iIntros "* H". iNamed "H".
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

Lemma prefix_lookup_agree {A} l1 l2 i (x1 x2 : A) :
  l1 `prefix_of` l2 ∨ l2 `prefix_of` l1 →
  l1 !! i = Some x1 →
  l2 !! i = Some x2 →
  x1 = x2.
Proof.
  intros Hpref Hlook1 Hlook2.
  destruct Hpref as [Hpref|Hpref].
  - opose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpref) as ?. by simplify_eq/=.
  - opose proof (prefix_lookup_Some _ _ _ _ Hlook2 Hpref) as ?. by simplify_eq/=.
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
    "Hown_err" ∷ ClientErr.own ptr_err err c.(Client.serv).(Server.sig_pk) ∗
    "Herr" ∷ if err.(ClientErr.Err) then True else
      ∀ adtr_γ,
      ("#His_pk" ∷ is_sig_pk adtr_pk (adtr_sigpred adtr_γ))
      -∗
      ("#His_audit" ∷ is_audit c.(Client.γ) adtr_γ c.(Client.serv_vrf_pk) c.(Client.next_epoch))
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
    "Herr" ∷ ClientErr.own ptr_err0 err0 c.(Client.serv).(Server.sig_pk) ∗
    "Hptr_err0" ∷ ptr2_err0 ↦[ptrT] #ptr_err0 ∗
    if negb err0.(ClientErr.Err) then
      ∃ sd',
      "%Hdom" ∷ ⌜ dom sd_ptrs' = dom sd' ⌝ ∗
      "%Hsub" ∷ ⌜ sd' ⊆ sd ⌝ ∗
      "#Hpost" ∷ ([∗ map] x ∈ sd', auditEpoch_post adtr_pk x)
    else True)%I with "Hown_sd_refs [$Hown_cli_adtr $Hptr_err0 Herr0]").
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
    iDestruct "Herr1" as "#Haudit".
    iNamedSuffix "Hown_err1" "1". wp_loadField. wp_if_destruct.
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
  assert (pred $ uint.nat c.(Client.next_epoch) =
    uint.nat (word.sub c.(Client.next_epoch) (W64 1))) as Heq_pred by word.
  rewrite Heq_pred in Hlast_dig.
  pose proof (Hagree_digs_sd _ _ Hlast_dig) as [? Hlook_sd].
  iDestruct (big_sepM_lookup with "Hpost") as "H"; [exact Hlook_sd|].
  iSpecialize ("H" with "His_pk"). iNamed "H". simpl in *.

  iExists (take (uint.nat c.(Client.next_epoch)) adtr_st). do 4 try iSplit.
  { iPureIntro. apply lookup_lt_Some in Hlook_dig.
    rewrite -Heq_pred in Hlook_dig.
    rewrite length_take_le; [done|lia]. }
  { iApply (mono_list_lb_own_le with "Hlb_adtr"). apply prefix_take. }
  { iApply (big_sepL_take with "Hdigs_adtr"). }
  { iPureIntro. rewrite fmap_take.
    refine (adtr_inv_prefix _ _ Hinv_adtr). apply prefix_take. }
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
  iDestruct (big_sepL_lookup with "Hdigs_adtr") as "Hmerk_dig"; [exact Hlook_dig|].
  iDestruct (is_merkle_entry_with_map with "Hhas_merk_proof Hmerk_dig") as %Hlook_final.
  iDestruct (mono_list_lb_valid with "Hlb_adtr0 Hlb_adtr") as %Hpref.
  apply lookup_take_Some in Hlook_adtr as [Hlook_adtr _].
  opose proof (prefix_lookup_agree _ _ _ _ _ Hpref Hlook_adtr Hlook_dig) as ?.
  rewrite lookup_fmap in Hlook_final. simplify_eq/=. naive_solver.
Qed.

*)
End proof.

(*
Definition lemmas := (@wp_NewClient, @wp_Client__Audit, @wp_Client__Get, @wp_Client__SelfMon, @wp_Client__Put).
Print Assumptions lemmas.

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
*)
