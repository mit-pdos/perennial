From New.generatedproof.github_com.sanjit_bhat.pav Require Import client server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc auditor cryptoffi hashchain ktcore merkle sigpred.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  server rpc.

(* TODO: i don't really know where [wp_CallHistory] should go.
it's halfway between server and client.
as such, it breaks some pkg abstractions. *)

Module client.
Import server.server rpc.server.

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

Definition valid obj : iProp Σ :=
  "%Hlast_dig" ∷ ⌜last obj.(digs) = Some obj.(dig)⌝ ∗
  "#His_chain" ∷ hashchain.is_chain obj.(digs) obj.(cut) obj.(link) (S $ uint.nat obj.(epoch)) ∗
  "#His_sig" ∷ ktcore.wish_LinkSig obj.(serv).(servInfo.sig_pk)
    obj.(epoch) obj.(link) obj.(sig).

Definition own ptr obj : iProp Σ :=
  ∃ sl_dig sl_link sl_sig,
  "#Hstruct_epoch" ∷ ptr ↦□ (client.epoch.mk obj.(epoch) sl_dig sl_link sl_sig) ∗
  "#Hsl_dig" ∷ sl_dig ↦*□ obj.(dig) ∗
  "#Hsl_link" ∷ sl_link ↦*□ obj.(link) ∗
  "#Hsl_sig" ∷ sl_sig ↦*□ obj.(sig) ∗

  "#Hvalid_epoch" ∷ valid obj.

(* separate [own] from [correct] to allow proving "pure" specs on [own]. *)
Definition correct obj γ : iProp Σ :=
  ∃ hist,
  "#His_hist" ∷ mono_list_lb_own γ.(server.cfg.histγ) hist ∗
  "%Heq_digs" ∷ ⌜obj.(digs) = hist.*1⌝ ∗
  "%Heq_cut" ∷ ⌜obj.(cut) = None⌝ ∗
  "%Heq_ep" ∷ ⌜length hist = S $ uint.nat obj.(epoch)⌝.

End proof.
End epoch.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition wish_getNextEp prev sigPk chainProof sig newDigs next : iProp Σ :=
  "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof newDigs⌝ ∗
  "#Hlen_vals" ∷
    (if decide (newDigs = [])
    then "%Heq_next" ∷ ⌜next = prev⌝
    else
      ∃ newEp newLink,
      "%HnewEp" ∷ ⌜uint.Z newEp = (uint.Z prev.(epoch.epoch) + length newDigs)%Z⌝ ∗
      "#His_new_chain" ∷ hashchain.is_chain (prev.(epoch.digs) ++ newDigs)
        prev.(epoch.cut) newLink (S $ uint.nat newEp) ∗
      "#Hwish_sig" ∷ ktcore.wish_LinkSig sigPk newEp newLink sig ∗
      "%Heq_next" ∷ ⌜next = epoch.mk' newEp (default [] (last newDigs))
        newLink sig (prev.(epoch.digs) ++ newDigs)
        prev.(epoch.cut) prev.(epoch.serv)⌝).

#[global] Instance wish_getNextEp_pers prev pk chain sig digs next :
  Persistent (wish_getNextEp prev pk chain sig digs next).
Proof. rewrite /wish_getNextEp. case_decide; apply _. Qed.

Lemma wish_getNextEp_det prev pk chain sig digs0 digs1 next0 next1 :
  wish_getNextEp prev pk chain sig digs0 next0 -∗
  wish_getNextEp prev pk chain sig digs1 next1 -∗
  ⌜digs0 = digs1 ∧ next0 = next1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  opose proof (hashchain.wish_Proof_det _ _ _ Hwish_chainProof0 Hwish_chainProof1) as ->.
  case_decide;
    iNamedSuffix "Hlen_vals0" "0";
    iNamedSuffix "Hlen_vals1" "1";
    [by simplify_eq/=|].
  iDestruct (hashchain.is_chain_det with "His_new_chain0 His_new_chain1") as %->.
  replace newEp with newEp0 in * by word.
  by simplify_eq/=.
Qed.

Lemma wp_CallHistory s γ (uid prevEpoch prevVerLen : w64) :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ ∗
    "#His_prevHist" ∷ match γ with None => True | Some cfg =>
      ∃ entry,
      let pks := entry.2 !!! uid in
      "#Hidx" ∷ mono_list_idx_own cfg.(cfg.histγ) (uint.nat prevEpoch) entry ∗
      "%Hver" ∷ ⌜uint.nat prevVerLen ≤ length pks⌝ end
  }}}
  @! server.CallHistory #s #uid #prevEpoch #prevVerLen
  {{{
    sl_chainProof sl_linkSig sl_hist ptr_bound err,
    RET (#sl_chainProof, #sl_linkSig, #sl_hist, #ptr_bound, #(ktcore.blame_to_u64 err));
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool γ]}⌝ ∗
    "Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ chainProof linkSig hist bound,
      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "Hgood" ∷ match γ with None => True | Some cfg =>
        ∀ prev,
        epoch.valid prev -∗
        epoch.correct prev cfg -∗
        ⌜prev.(epoch.epoch) = prevEpoch⌝ -∗

        ∃ servHist lastDig lastKeys next,
        let pks := lastKeys !!! uid in
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗
        "%Hlt_prevEpoch" ∷ ⌜uint.nat prevEpoch < length servHist⌝ ∗
        "%Hlt_prevVer" ∷ ⌜uint.nat prevVerLen ≤ length pks⌝ ∗
        (* TODO: add to serv specs and other methods. *)
        "%Hnoof_vers" ∷ ⌜length pks = sint.nat (W64 (length pks))⌝ ∗
        "%Hlast_servHist" ∷ ⌜last servHist = Some (lastDig, lastKeys)⌝ ∗

        "#Hwish_getNextEp" ∷ wish_getNextEp prev cfg.(cfg.sig_pk) chainProof
          linkSig (drop (S (uint.nat prevEpoch)) servHist.*1) next ∗
        "#Hgood_next" ∷ epoch.correct next cfg ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb cfg.(cfg.vrf_pk) uid prevVerLen
          next.(epoch.dig) hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb cfg.(cfg.vrf_pk) uid
          (W64 $ length pks) next.(epoch.dig) bound end)
  }}}.
Proof.
  wp_start as "@". wp_auto.
  wp_apply wp_alloc as "* Ha".
  wp_apply (HistoryArg.wp_enc (HistoryArg.mk' _ _ _) with "[$Ha]") as "* (Hsl_b&_&_&%Hwish)".
  { iDestruct own_slice_nil as "$".
    iDestruct own_slice_cap_nil as "$". }
  simpl in *.
  wp_apply wp_alloc as "* Hreply".
  wp_apply (wp_History_cli_call (Q_read (uint.nat prevEpoch))
    with "[$Hsl_b $Hreply]") as "* @".
  { iFrame "#". case_match; [|done].
    iNamed "His_prevHist".
    iModIntro. by iApply op_read. }
  wp_if_destruct.
  (* BlameUnknown only from network. *)
  { rewrite ktcore.rw_BlameUnknown.
    iApply "HΦ".
    iSplit; [|by case_decide].
    iPureIntro. apply ktcore.blame_unknown. }
  iNamed "Herr_net".
  iPersist "Hsl_reply".
  wp_apply (HistoryReply.wp_dec with "[$Hsl_reply]") as "* Hgenie".
  wp_if_destruct.
  (* serv promised well-encoded reply. *)
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iSplit; [|by case_decide].
    iApply ktcore.blame_one.
    iIntros (?).
    case_match; try done.
    iNamed "Hgood".
    iApply "Hgenie".
    naive_solver. }
  iDestruct "Hgenie" as (??) "(#Hreply&_&%His_dec)".
  destruct obj. iNamed "Hreply".
  wp_auto. simpl.
  rewrite -wp_fupd.
  wp_if_destruct.
  { rewrite ktcore.rw_BlameServFull.
    iApply "HΦ".
    iApply fupd_sep.
    iSplitL; try done.
    iApply ktcore.blame_one.
    (* instead of using [fupd_not_prop], another option is to change
    [BlameSpec] to allow proving contra under fupd. *)
    iApply fupd_not_prop.
    iIntros (?).
    case_match; try done.
    iNamed "Hgood".
    opose proof (HistoryReply.wish_det _ _ _ _ His_dec His_reply) as [? _].
    simplify_eq/=.
    iDestruct "Hgood" as "[@|@]".
    (* we gave well-encoded arg. *)
    - iApply "Hgenie". naive_solver.
    (* we gave valid decoded args. *)
    - opose proof (HistoryArg.wish_det _ _ _ _ Hwish Hdec) as [? _].
      simplify_eq/=.
      iDestruct "HQ" as "[#Hnew_hist %]".
      iDestruct "Herr_serv_args" as %[?|?].
      (* good prevEpoch. *)
      1: lia.
      (* good prevVerLen. *)
      iNamed "His_prevHist".
      iMod (len_pks_mono uid0 with "His_serv Hidx []") as %Hmono.
      2: {
        rewrite last_lookup in Hlast_hist.
        iDestruct (mono_list_idx_own_get with "Hnew_hist") as "H"; [done|].
        iFrame "H". }
      { word. }
      iPureIntro. simpl in *.
      remember (length (entry.2 !!! _)) as w.
      rewrite -Heqw in Hmono.
      word. }

  rewrite ktcore.rw_BlameNone.
  iApply "HΦ".
  iApply fupd_sep.
  iSplitR. { iPureIntro. apply ktcore.blame_none. }
  case_decide; try done.
  iFrame "#".
  case_match; try done.
  iNamed "Hgood".
  opose proof (HistoryReply.wish_det _ _ _ _ His_dec His_reply) as [? _].
  simplify_eq/=.
  iDestruct "Hgood" as "[@|@]"; try done.
  opose proof (HistoryArg.wish_det _ _ _ _ Hwish Hdec) as [? _].
  simplify_eq/=.
  iDestruct "HQ" as "[#Hnew_hist %]".
  iNamed "Herr_serv_args".
  iNamed "His_prevHist".
  iMod (len_pks_mono uid0 with "His_serv Hidx []") as %Hmono.
  2: {
    rewrite last_lookup in Hlast_hist.
    iDestruct (mono_list_idx_own_get with "Hnew_hist") as "H"; [done|].
    iFrame "H". }
  { word. }
  iModIntro.

  iIntros (?) "@ @ %Heq_prevEp".
  simplify_eq/=.
  iFrame (Hlast_hist) "Hnew_hist".
  iExists (epoch.mk' (W64 (length σ.(state.hist) - 1))
    lastDig lastLink
    (* sig is only thing that can't be determ generated. *)
    (if decide (drop (S (uint.nat prev.(epoch.epoch))) σ.(state.hist).*1 = [])
      then prev.(epoch.sig) else linkSig)
    σ.(state.hist).*1 None prev.(epoch.serv)).
  iFrame "#%". simpl in *.

  iSplit.
  { remember (length (entry.2 !!! _)) as w0.
    rewrite -Heqw0 in Hmono.
    remember (length (lastKeys !!! _)) as w1.
    rewrite -Heqw1.
    word. }
  iSplit.
  2: { iPureIntro. repeat split; try done.
    (* TODO[word]: shouldn't need to abstract out terms. *)
    remember (length σ.(state.hist)) as x.
    rewrite -Heqx.
    word. }

  case_decide as Hlen_vals.
  { iDestruct (mono_list_lb_valid with "His_hist Hnew_hist") as %Hpref.
    assert (hist0 = σ.(state.hist)) as ->.
    {
      apply (f_equal length) in Hlen_vals. simpl in *.
      rewrite length_drop in Hlen_vals.
      autorewrite with len in *.
      destruct Hpref as [Hpref|Hpref].
      - opose proof (prefix_length_eq _ _ Hpref _) as ->; [|done].
        remember (length σ.(state.hist)) as x.
        rewrite -Heqx in Hlen_vals |-*.
        word.
      - opose proof (prefix_length_eq _ _ Hpref _) as ->; [|done].
        remember (length σ.(state.hist)) as x.
        rewrite -Heqx.
        word. }
    rewrite Heq_ep.
    rewrite Heq_digs in Hlast_dig |-*.
    rewrite Heq_cut.
    iDestruct (hashchain.is_chain_det with "His_lastLink His_chain") as %->.
    iPureIntro. destruct prev. simpl in *. repeat f_equal; try done.
    - word.
    - apply (f_equal (fmap fst)) in Hlast_hist. simpl in *.
      rewrite -fmap_last Hlast_dig in Hlast_hist.
      by simplify_eq/=.
    - by case_decide. }

  iDestruct (mono_list_lb_valid with "His_hist Hnew_hist") as %[[newHist Ht]|Hpref].
  2: {
    apply prefix_length in Hpref.
    rewrite -skipn_all_iff in Hlen_vals.
    autorewrite with len in *. word. }
  rewrite ->Ht in *. clear Ht.
  rewrite {}Heq_digs {}Heq_cut.
  rewrite fmap_app drop_app_length' in Hlen_vals |-*; [|len].

  iExists (W64 (uint.Z prev.(epoch.epoch) + length newHist)), _.
  autorewrite with len in *.
  iSplit; [word|].
  iSplit. { iExactEq "His_lastLink". rewrite /named. repeat f_equal. word. }
  iSplit. { iExactEq "Hwish_linkSig". rewrite /named. repeat f_equal. word. }
  case_decide; try done.
  iPureIntro. repeat f_equal; [word|].
  destruct newHist using rev_ind; [done|]. clear IHnewHist.
  rewrite (assoc _) last_snoc in Hlast_hist.
  simplify_eq/=.
  by rewrite fmap_app last_snoc.
Qed.

End proof.
End client.
