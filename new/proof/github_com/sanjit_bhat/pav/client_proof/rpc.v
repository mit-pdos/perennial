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
    (* physical state. *)
    epoch: w64;
    dig: list w8;
    link: list w8;
    sig: list w8;

    (* externalize logical state relevant to getNextEp transition. *)
    digs: list (list w8);
    cut: option $ list w8;
  }.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition own ptr obj serv : iProp Σ :=
  ∃ sl_dig sl_link sl_sig,
  "#Hstruct_epoch" ∷ ptr ↦□ (client.epoch.mk obj.(epoch) sl_dig sl_link sl_sig) ∗
  "#Hsl_dig" ∷ sl_dig ↦*□ obj.(dig) ∗
  "#Hsl_link" ∷ sl_link ↦*□ obj.(link) ∗
  "#Hsl_sig" ∷ sl_sig ↦*□ obj.(sig) ∗

  "%Hlast_dig" ∷ ⌜last obj.(digs) = Some obj.(dig)⌝ ∗
  "#His_chain" ∷ hashchain.is_chain obj.(digs) obj.(cut) obj.(link)
    (S $ uint.nat obj.(epoch)) ∗
  "#His_sig" ∷ ktcore.wish_LinkSig serv.(servInfo.sig_pk)
    obj.(epoch) obj.(link) obj.(sig).

Definition align_serv obj γ : iProp Σ :=
  ∃ hist,
  "#His_hist" ∷ mono_list_lb_own γ.(server.cfg.histγ) hist ∗
  "%Heq_ep" ∷ ⌜length hist = S $ uint.nat obj.(epoch)⌝ ∗
  "%Heq_digs" ∷ ⌜obj.(digs) = hist.*1⌝ ∗
  "%Heq_cut" ∷ ⌜obj.(cut) = None⌝.

End proof.
End epoch.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

(* TODO: might be able to hide [newDigs]. *)
Definition wish_getNextEp prev sigPk chainProof sig newDigs next : iProp Σ :=
  ∃ nextEp nextDig nextLink,
  "%Heq_next" ∷ ⌜next = epoch.mk' nextEp nextDig nextLink sig
    (prev.(epoch.digs) ++ newDigs) prev.(epoch.cut)⌝ ∗
  "%HnextEp" ∷ ⌜uint.Z nextEp = (uint.Z prev.(epoch.epoch) + length newDigs)%Z⌝ ∗
  "%HnextDig" ∷ ⌜last next.(epoch.digs) = Some nextDig⌝ ∗
  "%HnewDigs" ∷ ⌜hashchain.wish_Proof chainProof newDigs⌝ ∗
  "#HnextLink" ∷ hashchain.is_chain next.(epoch.digs)
    next.(epoch.cut) nextLink (S $ uint.nat nextEp) ∗
  "#HnextSig" ∷ ktcore.wish_LinkSig sigPk nextEp nextLink sig.

Lemma wish_getNextEp_det prev pk chain sig digs0 digs1 next0 next1 :
  wish_getNextEp prev pk chain sig digs0 next0 -∗
  wish_getNextEp prev pk chain sig digs1 next1 -∗
  ⌜digs0 = digs1 ∧ next0 = next1⌝.
Proof.
  iNamedSuffix 1 "0".
  iNamedSuffix 1 "1".
  opose proof (hashchain.wish_Proof_det _ _ _ HnewDigs0 HnewDigs1) as ->.
  simplify_eq/=.
  iDestruct (hashchain.is_chain_det with "HnextLink0 HnextLink1") as %->.
  by replace nextEp with nextEp0 in * by word.
Qed.

Lemma wp_CallHistory s γ (uid prevEpoch prevVerLen : w64) :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ ∗
    (* one recurring pattern in pav is that resources only become available
    under a good flag. so far, i've been able to work around this.
    e.g., here, the caller needs to open invs after knowing good,
    so we add an update under the match. *)
    "#His_args" ∷ □ match γ with None => True | Some cfg =>
      |={⊤}=> ∃ (entry : list w8 * keys_ty),
      "#Hidx_ep" ∷ mono_list_idx_own cfg.(cfg.histγ) (uint.nat prevEpoch) entry ∗
      "%Hlt_ver" ∷ ⌜uint.nat prevVerLen ≤ length (entry.2 !!! uid)⌝ end
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
        epoch.align_serv prev cfg -∗
        ⌜prev.(epoch.epoch) = prevEpoch⌝ -∗

        ∃ servHist lastDig lastKeys next,
        let pks := lastKeys !!! uid in
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗
        "%Hlt_prevEpoch" ∷ ⌜uint.nat prevEpoch < length servHist⌝ ∗
        "%Hlt_prevVer" ∷ ⌜uint.nat prevVerLen ≤ length pks⌝ ∗
        (* TODO: add noof to serv specs and other methods. *)
        "%Hnoof_vers" ∷ ⌜length pks = sint.nat (W64 (length pks))⌝ ∗
        "%Hlast_servHist" ∷ ⌜last servHist = Some (lastDig, lastKeys)⌝ ∗

        "#Hwish_getNextEp" ∷ wish_getNextEp prev cfg.(cfg.sig_pk) chainProof
          linkSig (drop (S (uint.nat prevEpoch)) servHist.*1) next ∗
        "#Halign_next" ∷ epoch.align_serv next cfg ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb cfg.(cfg.vrf_pk) uid prevVerLen
          next.(epoch.dig) hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb cfg.(cfg.vrf_pk) uid
          (W64 $ length pks) next.(epoch.dig) bound ∗

        (* info in pending GS.
        caller could derive this itself when proving BlameSpec,
        but we'd rather not have a fupd in front of BlameSpec so that
        it's actually pers. *)
        "#Hpend_gs" ∷ (if decide (length pks = 0%nat) then True else
          ∃ uidγ,
          "%Hlook_uidγ" ∷ ⌜cfg.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
          "#Hidx_pks" ∷ ([∗ list] ver ↦ pk ∈ pks,
            ∃ i,
            mono_list_idx_own uidγ i ((W64 ver), pk))) end)
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
    iModIntro.
    iMod "His_args" as "@".
    by iApply op_read. }
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
    rewrite -fupd_not_prop.
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
      iMod "His_args" as "@".
      iMod (hist_pks_prefix uid0 with "His_serv Hidx_ep []") as %?%prefix_length.
      2: {
        rewrite last_lookup in Hlast_hist.
        iDestruct (mono_list_idx_own_get with "Hnew_hist") as "H"; [done|].
        iFrame "H". }
      { word. }
      iPureIntro. simpl in *.
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

  iMod "His_args" as "@".
  iMod (hist_pks_prefix uid0 with "His_serv Hidx_ep []") as %?%prefix_length.
  2: {
    rewrite last_lookup in Hlast_hist.
    iDestruct (mono_list_idx_own_get with "Hnew_hist") as "H"; [done|].
    iFrame "H". }
  { word. }
  iMod (put_op_records with "His_serv []") as "#Hrecords".
  { iApply (mono_list_idx_own_get with "Hnew_hist").
    by rewrite last_lookup in Hlast_hist. }
  iModIntro.

  iIntros (?) "@ %Heq_prevEp".
  simplify_eq/=.
  iFrame (Hlast_hist) "Hnew_hist".
  iExists (epoch.mk' (W64 (length σ.(state.hist) - 1)) lastDig lastLink linkSig
    σ.(state.hist).*1 None).
  iFrame "#%". simpl in *.

  iAssert (⌜hist0 `prefix_of` σ.(state.hist)⌝)%I as %[newDigs Ht].
  { iDestruct (mono_list_lb_valid with "His_hist Hnew_hist") as %[?|[newDigs ?]]; [done|].
    iPureIntro. simplify_eq/=.
    destruct newDigs; [by list_simplifier|].
    exfalso. autorewrite with len in *.
    word. }
  rewrite ->Ht in *. clear Ht.
  rewrite {}Heq_digs {}Heq_cut.
  rewrite fmap_app drop_app_length' in |-*; [|by len..].
  autorewrite with len in *.

  (* TODO: it'd be nice to have a tactic that iSplit's just the
  immediate chain of seps in goal. *)
  iSplit; [word|].
  iSplit.
  { iExists _.
    repeat iSplit; try iPureIntro; [done|word|..].
    - apply (f_equal (fmap fst)) in Hlast_hist. simpl in *.
      by rewrite -fmap_last fmap_app in Hlast_hist.
    - iExactEq "His_lastLink". rewrite /named. repeat f_equal. word. }
  iSplit. { iPureIntro. repeat split; try done. word. }
  { case_decide as Hlen_pks; try done.
    rewrite lookup_total_alt in Hlen_pks |-*.
    destruct (lastKeys !! uid0) eqn:Hlook_keys;
      rewrite Hlook_keys in Hlen_pks |-*; simpl in *; [|word].
    iDestruct ("Hrecords" with "[//][]") as "$". word. }
Qed.

End proof.
End client.
