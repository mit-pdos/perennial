From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde server.

(* notes:
- only change is that some of these specs return Blame (not bool) err.
- BlameUnknown is like giving up.
it gives the caller a trivial postcond.
since the req might not have even hit the serv, it's not in front of a Q.
- the postcond form with BlameUnknown is:
(∀ σ, Q σ -∗ err = other ∗ normal postcond -∗ Φ) ∗
(err = BlameUnknown -∗ Φ).
the client must prove both postconds.
the function can decide which postcond to use.
- the specs implicitly assume a good network pipeline to good serv.
under those conditions, the RPC client should encode args correctly,
the RPC server should decode args correctly,
the RPC server should encode replies correctly,
and the RPC client should decode replies correctly.
the specs capture this by not allowing errors from RPC serde.

TODO:
- for now, use same [is_Server] w/ same ptr arg. *)

Module server.
Import serde.server server.server.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Lemma wp_CallPut s γ uid pk sl_pk ver :
  ∀ Φ,
  is_pkg_init server -∗
  is_Server s γ -∗
  sl_pk ↦*□ pk -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    (own_Server γ (set state.pending (pure_put uid pk ver) σ) ={∅,⊤}=∗ True)) -∗
  ▷ Φ #() -∗
  WP @! server.CallPut #s #uid #sl_pk #ver {{ Φ }}.
Proof.
Admitted.

Lemma wp_CallHistory s γ (uid prevEpoch prevVerLen : w64) :
  ∀ Φ Q,
  is_pkg_init server -∗
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗ Q σ)) -∗
  (∀ σ sl_chainProof sl_linkSig sl_hist ptr_bound (err : ktcore.Blame),
    Q σ -∗
    ∃ lastDig lastKeys lastLink,
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗
    (
      "%Herr" ∷ ⌜err = {[ ktcore.BlameServFull ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist) ∨
        uint.nat prevVerLen > length pks⌝
      ∨
      ∃ chainProof linkSig hist bound,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist) ∧
        uint.nat prevVerLen ≤ length pks⌝ ∗

      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
        (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
      "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
        (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
      "#Hwish_hist" ∷ ktcore.wish_ListMemb γ.(cfg.vrf_pk) uid prevVerLen
        lastDig hist ∗
      "%Heq_hist" ∷ ⌜Forall2
        (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
        (drop (uint.nat prevVerLen) pks) hist⌝ ∗
      "#Hwish_bound" ∷ ktcore.wish_NonMemb γ.(cfg.vrf_pk) uid
        (W64 $ length pks) lastDig bound
    ) -∗
    Φ #(sl_chainProof, sl_linkSig, sl_hist, ptr_bound, err)) -∗
  (* TODO: unify into a disjunct with three branches. *)
  (* TODO: unify with isGood=false spec, which just gives decoding heap resources. *)
  (∀ (sl_chainProof sl_linkSig sl_hist : slice.t) (ptr_bound : loc) (err : ktcore.Blame),
    ⌜err = {[ ktcore.BlameUnknown ]}⌝ -∗
    Φ #(sl_chainProof, sl_linkSig, sl_hist, ptr_bound, err)) -∗
  WP @! server.CallHistory #s #uid #prevEpoch #prevVerLen {{ Φ }}.
Proof. Admitted.

Lemma wp_CallAudit s γ (prevEpoch : w64) :
  ∀ Φ Q,
  is_pkg_init server -∗
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗ Q σ)) -∗
  (∀ σ sl_proof (err : ktcore.Blame),
    Q σ -∗
    (
      "%Herr" ∷ ⌜err = {[ ktcore.BlameServFull ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist)⌝
      ∨
      ∃ proof prevDig,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist)⌝ ∗

      "#Hsl_proof" ∷ ktcore.AuditProofSlice1D.own sl_proof proof (□) ∗

      "%Heq_prevDig" ∷ ⌜σ.(state.hist).*1 !! (uint.nat prevEpoch) = Some prevDig⌝ ∗
      "#Hwish_digs" ∷ ktcore.wish_ListAudit prevDig proof
        (drop (S $ uint.nat prevEpoch) σ.(state.hist).*1) ∗
      "#His_sigs" ∷ ([∗ list] k ↦ aud ∈ proof,
        ∃ link,
        let ep := S $ (uint.nat prevEpoch + k)%nat in
        "#His_link" ∷ hashchain.is_chain (take (S ep) σ.(state.hist).*1)
          None link (S ep) ∗
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
          (W64 ep) link aud.(ktcore.AuditProof.LinkSig))
    ) -∗
    Φ #(sl_proof, err)) -∗
  (∀ (sl_proof : slice.t) (err : ktcore.Blame),
    ⌜err = {[ ktcore.BlameUnknown ]}⌝ -∗
    Φ #(sl_proof, err)) -∗
  WP @! server.CallAudit #s #prevEpoch {{ Φ }}.
Proof.
Admitted.

Lemma wp_CallStart s γ :
  ∀ Φ Q,
  is_pkg_init server -∗
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗ Q σ)) -∗
  (∀ σ ptr_chain ptr_vrf (err : ktcore.Blame),
    Q σ -∗
    ∃ chain vrf last_link,
    "%Herr" ∷ ⌜err = ∅⌝ ∗
    "#Hptr_chain" ∷ StartChain.own ptr_chain chain (□) ∗
    "#Hptr_vrf" ∷ StartVrf.own ptr_vrf vrf (□) ∗

    "#His_PrevLink" ∷ hashchain.is_chain
      (take (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)
      None chain.(StartChain.PrevLink)
      (uint.nat chain.(StartChain.PrevEpochLen)) ∗
    "%His_ChainProof" ∷ ⌜hashchain.wish_Proof chain.(StartChain.ChainProof)
      (drop (uint.nat chain.(StartChain.PrevEpochLen)) σ.(state.hist).*1)⌝ ∗
    "#His_last_link" ∷ hashchain.is_chain σ.(state.hist).*1 None
      last_link (length σ.(state.hist)) ∗
    "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(cfg.sig_pk)
      (W64 $ length σ.(state.hist) - 1) last_link chain.(StartChain.LinkSig) ∗

    "%Heq_VrfPk" ∷ ⌜γ.(cfg.vrf_pk) = vrf.(StartVrf.VrfPk)⌝ ∗
    "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(cfg.sig_pk) γ.(cfg.vrf_pk)
      vrf.(StartVrf.VrfSig) -∗
    Φ #(ptr_chain, ptr_vrf, err)) -∗
  (∀ (ptr_chain ptr_vrf : loc) (err : ktcore.Blame),
    ⌜err = {[ ktcore.BlameUnknown ]}⌝ -∗
    Φ #(ptr_chain, ptr_vrf, err)) -∗
  WP @! server.CallStart #s {{ Φ }}.
Proof.
Admitted.

End proof.
End server.
