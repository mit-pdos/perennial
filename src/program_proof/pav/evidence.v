From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle rpc invs.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.base_logic Require Import ghost_map.

Section evidence.
Context `{!heapGS Σ, !mono_listG gname Σ, !ghost_mapG Σ (list w8) (list w8)}.

Definition evidServLink_valid pk evid : iProp Σ :=
  ∃ link0 link1,
  is_hash
    (chainSepSome.encodesF (chainSepSome.mk
      evid.(evidServLink.epoch0)
      evid.(evidServLink.prevLink0)
      evid.(evidServLink.dig0)))
    link0 ∗
  is_hash
    (chainSepSome.encodesF (chainSepSome.mk
      evid.(evidServLink.epoch1)
      evid.(evidServLink.prevLink1)
      evid.(evidServLink.dig1)))
    link1 ∗
  is_sig pk (servSepLink.encodesF (servSepLink.mk link0)) evid.(evidServLink.sig0) ∗
  is_sig pk (servSepLink.encodesF (servSepLink.mk link1)) evid.(evidServLink.sig1).

Lemma wp_evidServLink_check ptr_evid evid sl_pk pk γ d0 :
  {{{
    "Hevid" ∷ evidServLink.own ptr_evid evid ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γ)
  }}}
  evidServLink__check #ptr_evid (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hvalid_sig" ∷ (evidServLink_valid pk evid -∗ ⌜ err = false ⌝) ∗
    if negb err then False else True
  }}}.
Proof. Admitted.
(*
  "#Hbind" ∷ is_hash (chainSepSome.encodesF (chainSepSome.mk epoch prevLink dig)) data.(servSepLink.link) ∗
  rewrite /evidServLink__check.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hevid".

  (* first link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep0) "Hptr_linkSep0".
  iDestruct (struct_fields_split with "Hptr_linkSep0") as "H";
    iNamed "H"; iClear "tag".
  iMod (own_slice_small_persist with "Hsl_prevLink0") as "#Hsl_prevLink0".
  wp_apply (chainSepSome.wp_encode with "[epoch prevLink data Hsl_prevLink0 Hsl_dig0]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink0, sl_dig0; iFrame "#∗".
  }
  iIntros (sl_link0Enc link0Enc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep0";
    iRename "Hsl_enc" into "Hsl_link0Enc";
    rename Henc into Henc_link0.
  wp_apply (wp_Hash with "Hsl_link0Enc");
    iIntros (sl_link0 link0) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_link0Enc";
    iRename "Hhash" into "Hsl_link0";
    iRename "His_hash" into "His_hash_link0".
  iMod (own_slice_small_persist with "Hsl_link0") as "#Hsl_link0".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_enc0) "Hptr_enc0".
  iDestruct (struct_fields_split with "Hptr_enc0") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_enc0 enc0) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_enc0";
    iRename "Hsl_enc" into "Hsl_enc0";
    rename Henc into Henc_enc0.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_enc0 Hsl_sig0]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_sig0";
    iRename "Hmsg" into "Hsl_enc0";
    iRename "HP" into "Hsigpred0".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* second link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep1) "Hptr_linkSep1".
  iDestruct (struct_fields_split with "Hptr_linkSep1") as "H";
    iNamed "H"; iClear "tag".
  iMod (own_slice_small_persist with "Hsl_prevLink1") as "#Hsl_prevLink1".
  wp_apply (chainSepSome.wp_encode with "[epoch prevLink data Hsl_prevLink1 Hsl_dig1]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink1, sl_dig1; iFrame "#∗".
  }
  iIntros (sl_link1Enc link1Enc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep1";
    iRename "Hsl_enc" into "Hsl_link1Enc";
    rename Henc into Henc_link1.
  wp_apply (wp_Hash with "Hsl_link1Enc");
    iIntros (sl_link1 link1) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_link1Enc";
    iRename "Hhash" into "Hsl_link1";
    iRename "His_hash" into "His_hash_link1".
  iMod (own_slice_small_persist with "Hsl_link1") as "#Hsl_link1".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_enc1) "Hptr_enc1".
  iDestruct (struct_fields_split with "Hptr_enc1") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_enc1 enc1) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_enc1";
    iRename "Hsl_enc" into "Hsl_enc1";
    rename Henc into Henc_enc1.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_enc1 Hsl_sig1]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_sig1";
    iRename "Hmsg" into "Hsl_enc1".
    iRename "HP" into "Hsigpred1".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* epochs are equal. *)
  wp_loadField.
  wp_loadField.
  wp_if_destruct; rename Heqb into Hepoch_eq.
  1: {
    (* TODO: why does:
      wp_apply (wp_BytesEqual "[$Hsl_link0 $Hsl_link1]").
      not work? *)
    wp_apply wp_BytesEqual; [iFrame "#"|].
    iIntros "_".
    case_bool_decide; [by iApply "HΦ"|]; rename H into Hlink_ne.
    destruct hon; [|by iApply "HΦ"].
    iDestruct "Hsigpred0" as "[[%sepLink0 [%Henc_link0' Hsigpred0]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }
    iDestruct "Hsigpred1" as "[[%sepLink1 [%Henc_link1' Hsigpred1]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }

    (* open binding, apply val divergence to prove false. *)
    iExFalso.
    rewrite ->Henc_link0' in Henc_enc0;
      apply servSepLink.inj in Henc_enc0 as ->.
    rewrite ->Henc_link1' in Henc_enc1;
      apply servSepLink.inj in Henc_enc1 as ->.
    iDestruct "Hsigpred0" as (epoch0 prevLink0 dig0) "H"; iNamed "H";
      iRename "Hbind" into "Hbind0";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr0".
    iDestruct "Hsigpred1" as (epoch1 prevLink1 dig1) "H"; iNamed "H";
      iRename "Hbind" into "Hbind1";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr1".
    iDestruct (hash_inj with "[$His_hash_link0] [$Hbind0]") as %->.
    iDestruct (hash_inj with "[$His_hash_link1] [$Hbind1]") as %->.
    apply chainSepSome.inj in Henc_link0 as [=]; subst.
    apply chainSepSome.inj in Henc_link1 as [=]; subst.
    iEval (rewrite Hepoch_eq) in "HidxCurr0".
    iDestruct (mono_list_idx_agree with "[$HidxCurr0] [$HidxCurr1]") as %[=].
    done.
  }

  (* epochs are off by one, but apart from that,
     almost same analysis as epoch equals case. *)
  wp_loadField.
  wp_loadField.
  wp_if_destruct; rename Heqb into Hepoch_off_eq.
  1: {
    wp_loadField.
    wp_apply wp_BytesEqual; [iFrame "#"|].
    iIntros "_".
    case_bool_decide; [by iApply "HΦ"|]; rename H into Hlink_ne.
    destruct hon; [|by iApply "HΦ"].
    iDestruct "Hsigpred0" as "[[%sepLink0 [%Henc_link0' Hsigpred0]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }
    iDestruct "Hsigpred1" as "[[%sepLink1 [%Henc_link1' Hsigpred1]] | [% [%Henc_put _]]]".
    2: { exfalso. eauto using servSep. }

    iExFalso.
    rewrite ->Henc_link0' in Henc_enc0;
      apply servSepLink.inj in Henc_enc0 as ->.
    rewrite ->Henc_link1' in Henc_enc1;
      apply servSepLink.inj in Henc_enc1 as ->.
    iDestruct "Hsigpred0" as (epoch0 prevLink0 dig0) "H"; iNamed "H";
      iRename "Hbind" into "Hbind0";
      iClear "HidxPrev";
      iRename "HidxCurr" into "HidxCurr0".
    iDestruct "Hsigpred1" as (epoc10 prevLink1 dig1) "H"; iNamed "H";
      iRename "Hbind" into "Hbind1";
      iRename "HidxPrev" into "HidxPrev1";
      iClear "HidxCurr".
    iDestruct (hash_inj with "[$His_hash_link0] [$Hbind0]") as %->.
    iDestruct (hash_inj with "[$His_hash_link1] [$Hbind1]") as %->.
    apply chainSepSome.inj in Henc_link0 as [=]; subst.
    apply chainSepSome.inj in Henc_link1 as [=]; subst.
    iEval (rewrite Hepoch_off_eq) in "HidxCurr0".
    iDestruct (mono_list_idx_agree with "[$HidxCurr0] [$HidxPrev1]") as %[=].
    done.
  }
  by iApply "HΦ".
Qed.
*)

Definition evidServPut_valid pk evid : iProp Σ :=
  ∃ link,
  is_hash
    (chainSepSome.encodesF (chainSepSome.mk
      evid.(evidServPut.epoch)
      evid.(evidServPut.prevLink)
      evid.(evidServPut.dig)))
    link ∗
  is_sig pk (servSepLink.encodesF (servSepLink.mk link)) evid.(evidServPut.linkSig) ∗
  is_sig pk
    (servSepPut.encodesF (servSepPut.mk
      evid.(evidServPut.epoch)
      evid.(evidServPut.id)
      evid.(evidServPut.val0)))
    evid.(evidServPut.putSig) ∗
  valid_merkle_proof
    evid.(evidServPut.proof)
    evid.(evidServPut.id)
    evid.(evidServPut.val1)
    evid.(evidServPut.dig).

Lemma wp_evidServPut_check ptr_evid evid sl_pk pk γ d0 :
  {{{
    "Hevid" ∷ evidServPut.own ptr_evid evid ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γ)
  }}}
  evidServPut__check #ptr_evid (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hvalid_evid" ∷ (evidServPut_valid pk evid -∗ ⌜ err = false ⌝) ∗
    if negb err then False else True
  }}}.
Proof. Admitted.
(*
  rewrite /evidServPut__check.
  iIntros (Φ) "H HΦ"; iNamed "H"; iNamed "Hevid".

  (* verify link sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_linkSep) "Hptr_linkSep".
  iMod (own_slice_small_persist with "Hsl_prevLink") as "#Hsl_prevLink".
  iMod (own_slice_small_persist with "Hsl_dig") as "#Hsl_dig".
  wp_apply (chainSepSome.wp_encode with "[Hptr_linkSep]").
  {
    instantiate (1:=chainSepSome.mk _ _ _).
    iDestruct (struct_fields_split with "Hptr_linkSep") as "H"; iNamed "H".
    rewrite /chainSepSome.own /=.
    iExists sl_prevLink, sl_dig; iFrame "#∗".
  }
  iIntros (sl_linkEnc linkEnc) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_linkSep";
    iRename "Hsl_enc" into "Hsl_linkEnc";
    rename Henc into Henc_link.
  wp_apply (wp_Hash with "Hsl_linkEnc");
    iIntros (sl_link link) "H"; iNamed "H";
    iRename "Hdata" into "Hsl_linkEnc";
    iRename "Hhash" into "Hsl_link";
    iRename "His_hash" into "His_hash_link".
  iMod (own_slice_small_persist with "Hsl_link") as "#Hsl_link".
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_preLinkSig) "Hptr_preLinkSig".
  iDestruct (struct_fields_split with "Hptr_preLinkSig") as "H";
    iNamed "H"; iClear "tag".
  wp_apply (servSepLink.wp_encode with "[link]").
  {
    instantiate (1:=servSepLink.mk _).
    rewrite /servSepLink.own /=.
    iFrame "#∗".
  }
  iIntros (sl_preLinkSig preLinkSig) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_preLinkSig";
    iRename "Hsl_enc" into "Hsl_preLinkSig";
    rename Henc into Henc_preLinkSig.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_preLinkSig Hsl_linkSig]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_linkSig";
    iRename "Hmsg" into "Hsl_preLinkSig";
    iRename "HP" into "HlinkSigPred".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* verify put promise sig. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_apply wp_allocStruct; [val_ty|];
    iIntros (ptr_strPrePut) "Hptr_strPrePut".
  iMod (own_slice_small_persist with "Hsl_id") as "#Hsl_id".
  iMod (own_slice_small_persist with "Hsl_val0") as "#Hsl_val0".
  wp_apply (servSepPut.wp_encode with "[Hptr_strPrePut]").
  {
    instantiate (1:=servSepPut.mk _ _ _).
    iDestruct (struct_fields_split with "Hptr_strPrePut") as "H"; iNamed "H".
    rewrite /servSepPut.own /=.
    iExists sl_id, sl_val0.
    iFrame "#∗".
  }
  iIntros (sl_prePut prePut) "H"; iNamed "H";
    iRename "Hobj" into "Hptr_prePut";
    iRename "Hsl_enc" into "Hsl_prePut";
    rename Henc into Henc_prePut.
  wp_loadField.
  wp_apply (wp_Verify with "[Hsl_prePut Hsl_putSig]"); [iFrame "#∗"|];
    iIntros (?) "H"; iNamed "H";
    iRename "Hsig" into "Hsl_putSig";
    iRename "Hmsg" into "Hsl_prePut";
    iRename "HP" into "HputSigPred".
  destruct ok.
  2: { wp_pures. by iApply "HΦ". }

  (* check merkle proof. *)
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  iMod (own_slice_small_persist with "Hsl_val1") as "#Hsl_val1".
  wp_apply (wp_CheckProof with "[Hid]"); [iFrame "#∗"|].
  iIntros (err0) "Herr0".
  destruct err0; [wp_pures; by iApply "HΦ"|].
  wp_loadField.
  wp_loadField.
  wp_apply wp_BytesEqual; [iFrame "#"|]; iIntros "_".

  (* final stretch. *)
  case_bool_decide; [by iApply "HΦ"|]; move: H => Hval_eq.
  destruct hon; [|by iApply "HΦ"].
  iExFalso.

  (* process link sig. *)
  iDestruct "HlinkSigPred" as "[[%sepLink [%Henc_link' #HlinkSigPred]] | [% [% _]]]".
  2: { exfalso. eauto using servSep. }
  rewrite ->Henc_link' in Henc_preLinkSig;
    apply servSepLink.inj in Henc_preLinkSig as ->.
  iDestruct "HlinkSigPred" as (epoch prevLink dig) "H"; iNamed "H";
    iClear "HidxPrev";
    iRename "HidxCurr" into "HidxCurr".
  iDestruct (hash_inj with "[$His_hash_link] [$Hbind]") as %->; iClear "Hbind".
  apply chainSepSome.inj in Henc_link as [=]; subst.

  (* process put sig. *)
  iDestruct "HputSigPred" as "[[% [% _]] | [%sepPut [%Henc_put' #HputSigPred]]]".
  { exfalso. eauto using servSep. }
  rewrite ->Henc_put' in Henc_prePut;
    apply servSepPut.inj in Henc_prePut as ->.
  iDestruct ("HputSigPred" $! link with "[$HidxCurr]") as "{HputSigPred} [%prevLink' [%dig' H]]";
    iNamed "H".
  simpl.
  iDestruct (hash_inj with "[$His_hash_link] [$Hbind]") as %Heq; iClear "Hbind".
  apply chainSepSome.inj in Heq as [=]; subst.

  (* derive contra from conflicting is_path_val's. *)
  iDestruct (is_path_val_inj with "[$Hmerkle] [$Herr0]") as %[=].
  done.
Qed.
*)
End evidence.
