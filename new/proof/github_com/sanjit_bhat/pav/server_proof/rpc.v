From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde server.

Notation HistoryRpc := 2 (only parsing).

(* notes:
- BlameUnknown is like giving up.
it gives the caller a trivial postcond.
since the request might not have even hit the serv, it's not in front of a Q.
- the specs implicitly assume a good network pipeline to good serv.
under those conditions, the RPC client should encode args correctly,
the RPC server should decode args correctly,
the RPC server should encode replies correctly,
and the RPC client should decode replies correctly.
the specs capture this by not allowing errors from RPC serde. *)

Module server.
Import serde.server server.server.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Definition is_Server_rpc (s : loc) (γ : option cfg.t) : iProp Σ :=
  match γ with None => True | Some cfg => is_serv_inv cfg end.

#[global] Instance is_Server_rpc_pers s γ : Persistent (is_Server_rpc s γ).
Proof. apply _. Qed.

Lemma wp_CallPut s γ uid sl_pk pk ver :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ ∗
    "#Hsl_pk" ∷ sl_pk ↦*□ pk ∗
    "#His_put" ∷ match γ with None => True | Some cfg =>
      ∃ i uidγ,
      "%Hlook_uidγ" ∷ ⌜cfg.(cfg.uidγ) !! uid = Some uidγ⌝ ∗
      "#Hidx" ∷ mono_list_idx_own uidγ i (ver, pk) end
  }}}
  @! server.CallPut #s #uid #sl_pk #ver
  {{{ RET #(); True }}}.
Proof. Admitted.

Lemma wp_History_cli_call (Q : cfg.t → state.t → iProp Σ)
    s γ sl_arg d0 arg ptr_reply (x : slice.t) :
  {{{
    is_pkg_init server ∗
    (* TODO: overloading is_Server_rpc. *)
    "#His_serv" ∷ is_Server_rpc s γ ∗
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ x ∗
    "#Hfupd" ∷ match γ with None => True | Some cfg =>
      □ (|={⊤,∅}=> ∃ σ, own_Server cfg σ ∗ (own_Server cfg σ ={∅,⊤}=∗ Q cfg σ)) end
  }}}
  s @ (ptrT.id advrpc.Client.id) @ "Call" #(W64 HistoryRpc) #sl_arg #ptr_reply
  {{{
    sl_reply err0, RET #err0;
    "Hsl_arg" ∷ sl_arg ↦*{d0} arg ∗
    "Hptr_reply" ∷ ptr_reply ↦ sl_reply ∗

    "Herr_net" ∷ match err0 with true => True | false =>
    ∃ replyB,
    "Hsl_reply" ∷ sl_reply ↦* replyB ∗

    "Hgood" ∷ match γ with None => True | Some cfg =>
    ∃ chainProof linkSig hist bound err1,
    "%His_reply" ∷ ⌜HistoryReply.wish replyB
      (HistoryReply.mk' chainProof linkSig hist bound err1) []⌝ ∗

    (* align with serv rpc rcvr, which doesn't know encoded args in precond. *)
    (("%Herr_serv_dec" ∷ ⌜err1 = true⌝ ∗
      "Hgenie" ∷ ¬ ⌜∃ obj tail, HistoryArg.wish arg obj tail⌝) ∨

    ∃ uid prevEpoch prevVerLen tail lastDig lastKeys lastLink σ,
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "%Hdec" ∷ ⌜HistoryArg.wish arg
      (HistoryArg.mk' uid prevEpoch prevVerLen) tail⌝ ∗
    "HQ" ∷ Q cfg σ ∗
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗

    "#Herr_serv_args" ∷
      match err1 with
      | true => ⌜uint.nat prevEpoch ≥ length σ.(state.hist) ∨
        uint.nat prevVerLen > length pks⌝
      | false =>
        "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
          (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig cfg.(cfg.sig_pk)
          (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb cfg.(cfg.vrf_pk) uid prevVerLen
          lastDig hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb cfg.(cfg.vrf_pk) uid
          (W64 $ length pks) lastDig bound
      end) end end
  }}}.
Proof. Admitted.

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
    RET (#sl_chainProof, #sl_linkSig, #sl_hist, #ptr_bound, #err);
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool γ]}⌝ ∗
    "Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ chainProof linkSig hist bound,
      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "Hgood" ∷ match γ with None => True | Some cfg =>
        ∃ servHist lastDig lastKeys lastLink,
        let numEps := length servHist in
        let pks := lastKeys !!! uid in
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗
        "%Hlen_epochs" ∷ ⌜uint.nat prevEpoch < numEps⌝ ∗
        "%Hlen_vers" ∷ ⌜uint.nat prevVerLen ≤ length pks⌝ ∗
        "%Hlast_servHist" ∷ ⌜last servHist = Some (lastDig, lastKeys)⌝ ∗
        "#His_lastLink" ∷ hashchain.is_chain servHist.*1 None lastLink numEps ∗

        "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
          (drop (S (uint.nat prevEpoch)) servHist.*1)⌝ ∗
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig cfg.(cfg.sig_pk)
          (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
        "#Hwish_hist" ∷ ktcore.wish_ListMemb cfg.(cfg.vrf_pk) uid prevVerLen
          lastDig hist ∗
        "%Heq_hist" ∷ ⌜Forall2
          (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
          (drop (uint.nat prevVerLen) pks) hist⌝ ∗
        "#Hwish_bound" ∷ ktcore.wish_NonMemb cfg.(cfg.vrf_pk) uid
          (W64 $ length pks) lastDig bound end)
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
  iFrame "#%".
  iNamed "His_prevHist".
  iMod (len_pks_mono uid0 with "His_serv Hidx []") as %Hmono.
  2: {
    rewrite last_lookup in Hlast_hist.
    iDestruct (mono_list_idx_own_get with "Hnew_hist") as "H"; [done|].
    iFrame "H". }
  { word. }
  iPureIntro. simpl in *.
  remember (length (entry.2 !!! _)) as w0.
  rewrite -Heqw0 in Hmono.
  remember (length (lastKeys !!! _)) as w1.
  rewrite -Heqw1.
  word.
Qed.

Lemma wp_CallAudit s γ (prevEpoch : w64) :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ ∗
    "#His_prevHist" ∷ match γ with None => True | Some cfg =>
      ∃ entry,
      "#Hidx" ∷ mono_list_idx_own cfg.(cfg.histγ) (uint.nat prevEpoch) entry end
  }}}
  @! server.CallAudit #s #prevEpoch
  {{{
    sl_proof err, RET (#sl_proof, #err);
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool γ]}⌝ ∗
    "Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ proof,
      "#Hsl_proof" ∷ ktcore.AuditProofSlice1D.own sl_proof proof (□) ∗

      "Hgood" ∷ match γ with None => True | Some cfg =>
        ∃ servHist prevDig,
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗
        "%Hlen_epochs" ∷ ⌜uint.nat prevEpoch < length servHist⌝ ∗
        "%Heq_prevDig" ∷ ⌜servHist.*1 !! (uint.nat prevEpoch) = Some prevDig⌝ ∗

        "#Hwish_digs" ∷ ktcore.wish_ListAudit prevDig proof
          (drop (S $ uint.nat prevEpoch) servHist.*1) ∗
        "#His_sigs" ∷ ([∗ list] k ↦ aud ∈ proof,
          ∃ link,
          let ep := S $ (uint.nat prevEpoch + k)%nat in
          "#His_link" ∷ hashchain.is_chain (take (S ep) servHist.*1)
            None link (S ep) ∗
          "#Hwish_linkSig" ∷ ktcore.wish_LinkSig cfg.(cfg.sig_pk)
            (W64 ep) link aud.(ktcore.AuditProof.LinkSig)) end)
  }}}.
Proof. Admitted.

Lemma wp_CallStart s γ :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ
  }}}
  @! server.CallStart #s
  {{{
    ptr_chain ptr_vrf err, RET (#ptr_chain, #ptr_vrf, #err);
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool γ]}⌝ ∗
    "Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ chain vrf,
      "#Hptr_chain" ∷ StartChain.own ptr_chain chain (□) ∗
      "#Hptr_vrf" ∷ StartVrf.own ptr_vrf vrf (□) ∗

      "Hgood" ∷ match γ with None => True | Some cfg =>
        ∃ servHist last_link,
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗

        "%His_PrevEpochLen" ∷ ⌜uint.nat chain.(StartChain.PrevEpochLen) < length servHist⌝ ∗
        "#His_PrevLink" ∷ hashchain.is_chain
          (take (uint.nat chain.(StartChain.PrevEpochLen)) servHist.*1)
          None chain.(StartChain.PrevLink)
          (uint.nat chain.(StartChain.PrevEpochLen)) ∗
        "%His_ChainProof" ∷ ⌜hashchain.wish_Proof chain.(StartChain.ChainProof)
          (drop (uint.nat chain.(StartChain.PrevEpochLen)) servHist.*1)⌝ ∗
        "#His_last_link" ∷ hashchain.is_chain servHist.*1 None
          last_link (length servHist) ∗
        "#His_LinkSig" ∷ ktcore.wish_LinkSig cfg.(cfg.sig_pk)
          (W64 $ length servHist - 1) last_link chain.(StartChain.LinkSig) ∗

        "%Heq_VrfPk" ∷ ⌜cfg.(cfg.vrf_pk) = vrf.(StartVrf.VrfPk)⌝ ∗
        "#His_VrfSig" ∷ ktcore.wish_VrfSig cfg.(cfg.sig_pk) cfg.(cfg.vrf_pk)
          vrf.(StartVrf.VrfSig) end)
  }}}.
Proof. Admitted.

End proof.
End server.
