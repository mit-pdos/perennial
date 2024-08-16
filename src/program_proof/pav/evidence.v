From Perennial.program_proof Require Import grove_prelude.
From Goose.github_com.mit_pdos.pav Require Import ktmerkle.

From Perennial.program_proof.pav Require Import common cryptoffi merkle rpc invs.
From Perennial.program_proof Require Import std_proof.
From iris.unstable.base_logic Require Import mono_list.
From Perennial.base_logic Require Import ghost_map.

Section evidence.
Context `{!heapGS Σ, !pavG Σ}.

Definition valid_signedLink pk (obj : signedLink.t) link : iProp Σ :=
  is_link_conn obj.(signedLink.epoch) obj.(signedLink.prevLink)
    obj.(signedLink.dig) link ∗
  is_sig pk (servSepLink.encodesF (servSepLink.mk link)) obj.(signedLink.sig).

Definition valid_signedPut pk (obj : signedPut.t) : iProp Σ :=
  is_sig
    pk
    (servSepPut.encodesF (servSepPut.mk
      obj.(signedPut.epoch) obj.(signedPut.id) obj.(signedPut.val)))
    obj.(signedPut.sig).

Definition valid_evidServLink pk (obj : evidServLink.t) : iProp Σ :=
  ∃ link0 link1,
  valid_signedLink pk (obj.(evidServLink.sigLn0)) link0 ∗
  valid_signedLink pk (obj.(evidServLink.sigLn1)) link1 ∗
  let epoch0 := obj.(evidServLink.sigLn0).(signedLink.epoch) in
  let epoch1 := obj.(evidServLink.sigLn1).(signedLink.epoch) in
  let prevLink1 := obj.(evidServLink.sigLn1).(signedLink.prevLink) in
  ⌜ (epoch0 = epoch1 ∧ link0 ≠ link1)
    ∨
    (epoch0 = word.sub epoch1 (W64 1) ∧ link0 ≠ prevLink1) ⌝.

Definition valid_evidServPut pk (obj : evidServPut.t) : iProp Σ :=
  ∃ link,
  valid_signedLink pk (obj.(evidServPut.sigLn)) link ∗
  valid_signedPut pk (obj.(evidServPut.sigPut)) ∗
  valid_merkle_proof
    obj.(evidServPut.proof)
    obj.(evidServPut.sigPut).(signedPut.id)
    obj.(evidServPut.val)
    obj.(evidServPut.sigLn).(signedLink.dig) ∗
  let epochLn := obj.(evidServPut.sigLn).(signedLink.epoch) in
  let epochPut := obj.(evidServPut.sigPut).(signedPut.epoch) in
  ⌜ epochLn = epochPut ⌝.

Lemma wp_signedLink_check ptr_sigLn sigLn sl_pk pk γ d0 :
  {{{
    signedLink.own ptr_sigLn sigLn ∗
    own_slice_small sl_pk byteT d0 pk ∗
    is_pk pk (serv_sigpred γ)
  }}}
  signedLink__check #ptr_sigLn (slice_val sl_pk)
  {{{
    sl_link (link : list w8) (err : bool), RET (slice_val sl_link, #err);
    signedLink.own ptr_sigLn sigLn ∗
    own_slice_small sl_pk byteT d0 pk ∗
    own_slice_small sl_link byteT (DfracOwn 1) link ∗
    (* in no err case, this lets us learn enough about the link
    to tie down Hvalid_err. *)
    is_link_conn sigLn.(signedLink.epoch) sigLn.(signedLink.prevLink)
      sigLn.(signedLink.dig) link ∗
    (valid_signedLink pk sigLn link -∗ ⌜ err = false ⌝) ∗
    if negb err then valid_signedLink pk sigLn link else True
  }}}.
Proof. Admitted.
(*
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
*)

Lemma wp_evidServLink_check ptr_evid evid sl_pk pk γ d0 :
  {{{
    evidServLink.own ptr_evid evid ∗
    own_slice_small sl_pk byteT d0 pk ∗
    is_pk pk (serv_sigpred γ)
  }}}
  evidServLink__check #ptr_evid (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    evidServLink.own ptr_evid evid ∗
    own_slice_small sl_pk byteT d0 pk ∗
    (valid_evidServLink pk evid -∗ ⌜ err = false ⌝) ∗
    if negb err then
      False ∗
      valid_evidServLink pk evid
    else True
  }}}.
Proof.
  rewrite /evidServLink__check.
  iIntros (Φ) "((%&%& HsigLn0 & Hptr_sigLn0 & HsigLn1 & Hptr_sigLn1)
    & Hsl_pk & #His_pk) HΦ".

  (* check signed links. *)
  wp_loadField.
  wp_apply (wp_signedLink_check with "[$HsigLn0 $Hsl_pk $His_pk]").
  iIntros (sl_link0 link0 err0)
    "(HsigLn0 & Hsl_pk & Hsl_link0 & #His_conn0 & Hgenie0 & Herr0)".
  wp_if_destruct.
  (* error. first signed link didn't validate. *)
  { iApply "HΦ". iFrame "HsigLn0 HsigLn1 ∗".
    iIntros "!> (%&%& #(His_conn0' & His_sig0') &_&_)".
    iDestruct (is_link_conn_agree_l with "His_conn0 His_conn0'") as %<-.
    iDestruct ("Hgenie0" with "[$His_conn0' $His_sig0']") as %[=]. }
  iDestruct "Herr0" as "#Hvalid_sigLn0".
  wp_loadField.
  wp_apply (wp_signedLink_check with "[$HsigLn1 $Hsl_pk $His_pk]").
  iIntros (sl_link1 link1 err1)
    "(HsigLn1 & Hsl_pk & Hsl_link1 & #His_conn1 & Hgenie1 & Herr1)".
  wp_if_destruct.
  (* error. second signed link didn't validate. *)
  { iApply "HΦ". iFrame "HsigLn0 HsigLn1 ∗".
    iIntros "!> (%&%&_& #(His_conn1' & His_sig1') &_)".
    iDestruct (is_link_conn_agree_l with "His_conn1 His_conn1'") as %<-.
    iDestruct ("Hgenie1" with "[$His_conn1' $His_sig1']") as %[=]. }
  iDestruct "Herr1" as "#Hvalid_sigLn1".

  (* check that links actually differ. *)
  iDestruct "HsigLn0" as "(%&%&%&%&%&%& Hptr_epoch0 & Hptr_prevLink0 &
    Hsl_prevLink0 & Hptr_dig0 & Hsl_dig0 & Hptr_sig0 & Hsl_sig0)".
  iDestruct "HsigLn1" as "(%&%&%&%&%&%& Hptr_epoch1 & Hptr_prevLink1 &
    Hsl_prevLink1 & Hptr_dig1 & Hsl_dig1 & Hptr_sig1 & Hsl_sig1)".
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_if_destruct; move: Heqb1 => Heq_epoch0.
  {
    wp_apply (wp_BytesEqual with "[$Hsl_link0 $Hsl_link1]").
    iIntros "[Hsl_link0 Hsl_link1]".
    case_bool_decide as Heq_links; iApply "HΦ".
    -
      (* error. links shouldn't be equal. *)
      iFrame "Hptr_sigLn0 ∗".
      (* TODO: not sure why iFrame doesn't handle the True here,
      even tho it does above. *)
      iSplit; [|done].

      iIntros "(%&%& #(His_conn0' &_) & #(His_conn1' &_) & %Heq_links')".
      iDestruct (is_link_conn_agree_l with "His_conn0 His_conn0'") as %<-.
      iDestruct (is_link_conn_agree_l with "His_conn1 His_conn1'") as %<-.

      iPureIntro.
      destruct Heq_links' as [[_ ?] | [Heq _]]; [done|].
      rewrite Heq_epoch0 in Heq.
      assert (∀ (x : w64), x ≠ word.sub x (W64 1)) as ?.
      { intros ? H%(f_equal (word.sub x)). by ring_simplify in H. }
      naive_solver.
    -
      (* no error. derive contra from two diff signed links at same epoch. *)
      iAssert (valid_evidServLink pk evid) as "Hvalid_evid".
      { iFrame "#". naive_solver. }
      iFrame "Hptr_sigLn0 ∗#".
      iSplit; [naive_solver|].
      iClear "Hvalid_evid ∗".

      (* extract lookups from sigs. *)
      iDestruct "Hvalid_sigLn0" as "(_ & His_sig0)".
      iDestruct "Hvalid_sigLn1" as "(_ & His_sig1)".
      iDestruct (is_sig_to_pred with "His_pk His_sig0") as "{His_sig0} HP0".
      iDestruct (is_sig_to_pred with "His_pk His_sig1") as "{His_pk His_sig1} HP1".
      iDestruct (get_serv_sigpred_link with "HP0") as "{HP0} HP0".
      iDestruct (get_serv_sigpred_link with "HP1") as "{HP1} HP1".
      iDestruct "HP0" as "(%&%&%&%& His_comm_st0 & His_conn0' & %Hlook0)".
      iDestruct "HP1" as "(%&%&%&%& His_comm_st1 & His_conn1' & %Hlook1)".
      iDestruct (is_link_conn_agree_r with "His_conn0 His_conn0'") as %(<-&<-&<-).
      iDestruct (is_link_conn_agree_r with "His_conn1 His_conn1'") as %(<-&<-&<-).
      iDestruct (is_committed_state_links_prefix with "His_comm_st0 His_comm_st1")
        as %Hpref.

      iPureIntro.
      rewrite -Heq_epoch0 in Hlook1.
      destruct Hpref as [Hpref | Hpref].
      { pose proof (prefix_lookup_Some _ _ _ _ Hlook0 Hpref) as ?. naive_solver. }
      { pose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpref) as ?. naive_solver. }
  }
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_loadField.
  wp_if_destruct; move: Heqb1 => Heq_epoch1.
  {
    wp_loadField.
    wp_loadField.
    wp_apply (wp_BytesEqual with "[$Hsl_link0 $Hsl_prevLink1]").
    iIntros "[Hsl_link0 Hsl_prevLink1]".
    case_bool_decide as Heq_links; iApply "HΦ".
    -
      (* error. links shouldn't be equal. *)
      iFrame "Hptr_sigLn0 ∗".
      (* TODO: not sure why iFrame doesn't handle the True here,
      even tho it does above. *)
      iSplit; [|done].

      iIntros "(%&%& #(His_conn0' &_) & #(His_conn1' &_) & %Heq_links')".
      iDestruct (is_link_conn_agree_l with "His_conn0 His_conn0'") as %<-.
      iDestruct (is_link_conn_agree_l with "His_conn1 His_conn1'") as %<-.

      iPureIntro.
      destruct Heq_links' as [[Heq _] | [_ ?]]; [|done].
      rewrite Heq_epoch1 in Heq.
      assert (∀ (x : w64), x ≠ word.sub x (W64 1)) as ?.
      { intros ? H%(f_equal (word.sub x)). by ring_simplify in H. }
      naive_solver.
    -
      (* no error. derive contra from prev.link differing from curr.prevLink. *)
      iAssert (valid_evidServLink pk evid) as "Hvalid_evid".
      { iFrame "#". naive_solver. }
      iFrame "Hptr_sigLn0 ∗#".
      iSplit; [naive_solver|].
      iClear "Hvalid_evid ∗".

      (* extract lookups from sigs. *)
      iDestruct "Hvalid_sigLn0" as "(_ & His_sig0)".
      iDestruct "Hvalid_sigLn1" as "(_ & His_sig1)".
      iDestruct (is_sig_to_pred with "His_pk His_sig0") as "{His_sig0} HP0".
      iDestruct (is_sig_to_pred with "His_pk His_sig1") as "{His_pk His_sig1} HP1".
      iDestruct (get_serv_sigpred_link with "HP0") as "{HP0} HP0".
      iDestruct (get_serv_sigpred_link with "HP1") as "{HP1} HP1".
      iDestruct "HP0" as "(%&%&%&%& His_comm_st0 & His_conn0' & %Hlook0)".
      iDestruct "HP1" as "(%&%&%&%& His_comm_st1 & His_conn1' & %Hlook1)".
      iDestruct (is_link_conn_agree_r with "His_conn0 His_conn0'") as %(<-&<-&<-).
      iDestruct (is_link_conn_agree_r with "His_conn1 His_conn1'") as %(<-&<-&<-).
      iDestruct (is_committed_state_links_prefix with "His_comm_st0 His_comm_st1")
        as %Hpref.

      iPureIntro.
      simpl in *.
      rewrite Heq_epoch1 in Hlook0.
      (*
      Hlook0: links0 !! (epoch1 - 1) = Some link0.
      Hlook1: links1 !! epoch1 = Some link1.
      from Hlook1, should derive that:
      links1 !! (epoch1 - 1) = Some prevLink1.

      how?
      from link sigpred, know that a specific link is smth.
      also have prevLink tied into there with is_conn.
      from committed state (binds), should be able to derive that
      adjacent lookups tied together by conn.

      binds says that prefixes of digs match up to links.
      should be not too bad to prove:
      is_link digs prevLink -∗
      is_link (digs ++ [new_dig]) link -∗
      is_link_conn prevLink new_dig link.
      *)
      destruct Hpref as [Hpref | Hpref].
      { pose proof (prefix_lookup_Some _ _ _ _ Hlook0 Hpref) as ?. naive_solver. }
      { pose proof (prefix_lookup_Some _ _ _ _ Hlook1 Hpref) as ?. naive_solver. }

(*
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

Lemma wp_evidServPut_check ptr_evid evid sl_pk pk γ d0 :
  {{{
    "Hevid" ∷ evidServPut.own ptr_evid evid ∗
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "#Hpk" ∷ is_pk pk (serv_sigpred γ)
  }}}
  evidServPut__check #ptr_evid (slice_val sl_pk)
  {{{
    (err : bool), RET #err;
    "Hsl_pk" ∷ own_slice_small sl_pk byteT d0 pk ∗
    "Hvalid_evid" ∷ (valid_evidServPut pk evid -∗ ⌜ err = false ⌝) ∗
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
