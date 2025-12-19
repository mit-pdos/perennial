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
    "%Hnoof_epochs" ∷ ⌜numEps = sint.nat (W64 numEps)⌝ ∗
    "%Hnoof_vers" ∷ ⌜length pks = sint.nat (W64 (length pks))⌝ ∗
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
    sl_proof err, RET (#sl_proof, #(ktcore.blame_to_u64 err));
    "%Hblame" ∷ ⌜ktcore.BlameSpec err {[ktcore.BlameServFull:=option_bool γ]}⌝ ∗
    "Herr" ∷ (if decide (err ≠ ∅) then True else
      ∃ proof,
      "#Hsl_proof" ∷ ktcore.AuditProofSlice1D.own sl_proof proof (□) ∗

      "Hgood" ∷ match γ with None => True | Some cfg =>
        ∃ servHist prevDig,
        "#Hlb_servHist" ∷ mono_list_lb_own cfg.(cfg.histγ) servHist ∗
        "%Hlen_epochs" ∷ ⌜uint.nat prevEpoch < length servHist⌝ ∗
        "%Heq_prevDig" ∷ ⌜servHist.*1 !! (uint.nat prevEpoch) = Some prevDig⌝ ∗

        "#Hwish_proof" ∷ ktcore.wish_ListAudit prevEpoch
          (take (S $ uint.nat prevEpoch) servHist.*1)
          None cfg.(cfg.sig_pk) proof
          (drop (S $ uint.nat prevEpoch) servHist.*1) end)
  }}}.
Proof. Admitted.

Lemma wp_CallStart s γ :
  {{{
    is_pkg_init server ∗
    "#His_serv" ∷ is_Server_rpc s γ
  }}}
  @! server.CallStart #s
  {{{
    ptr_chain ptr_vrf err, RET (#ptr_chain, #ptr_vrf, #(ktcore.blame_to_u64 err));
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
