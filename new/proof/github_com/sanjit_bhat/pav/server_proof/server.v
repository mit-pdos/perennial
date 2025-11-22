From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav.server_proof Require Import
  serde.

From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module server.
Import serde.server.

(* gmap from uid's to list of pks (indexed by version). *)
Definition keys_ty := gmap w64 (list $ list w8).

Module state.
Record t :=
  mk {
    (* pending map of all keys.
    client gives server permission to add to this. *)
    pending: keys_ty;
    (* history of digs and keys.
    server can update this by adding dig that corresponds to curr pending. *)
    (* TODO: technically, keys can be derived from dig,
    just like we derive links from digs in below specs. *)
    (* NOTE: all read-only post-conds only reference hist. *)
    hist: list (list w8 * keys_ty);
  }.
End state.

Module serverγ.
Record t :=
  mk {
    sig_pk: list w8;
    vrf_pk: list w8;
  }.
End serverγ.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Implicit Types γ : serverγ.t.
Implicit Types σ : state.t.

Axiom is_Server : ∀ (s : loc) γ, iProp Σ.

Axiom own_Server : ∀ γ σ, iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Definition pure_put σ uid pk (ver : w64) :=
  let pks := σ.(state.pending) !!! uid in
  (* drop put if not right version. *)
  if bool_decide (uint.nat ver ≠ length pks) then σ else
  set state.pending (<[uid:=pks ++ [pk]]>) σ.

(* RPC spec needs □ in front of atomic update. *)
Lemma wp_Server_Put s γ uid pk sl_pk ver :
  ∀ Φ,
  is_Server s γ -∗
  sl_pk ↦*□ pk -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    (own_Server γ (pure_put σ uid pk ver) ={∅,⊤}=∗ True)) ∗
  (* fupd might be used after Put returns, so Φ goes separately. *)
  Φ #() -∗
  WP s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver {{ Φ }}.
Proof.
Admitted.

(* The RPC spec is the same, no □ bc this doesn't mutate σ. *)
(* for idiomatic spec, use GS to contradict BlameUnknown. *)
Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) :
  ∀ Φ,
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ sl_chainProof sl_linkSig sl_hist ptr_bound (err : ktcore.Blame)
      lastDig lastKeys lastLink,
    let numEps := length σ.(state.hist) in
    let pks := lastKeys !!! uid in
    "%Hlast_hist" ∷ ⌜last σ.(state.hist) = Some (lastDig, lastKeys)⌝ ∗
    "#His_lastLink" ∷ hashchain.is_chain σ.(state.hist).*1 None lastLink numEps ∗
    ((
      "%Herr" ∷ ⌜err = {[ ktcore.BlameUnknown ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist) ∨
        uint.nat prevVerLen > length pks⌝
    ) ∨ (
      ∃ chainProof (linkSig : list w8) hist bound,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist) ∧
        uint.nat prevVerLen ≤ length pks⌝ ∗

      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ ktcore.MembSlice1D.own sl_hist hist (□) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "%Hwish_chainProof" ∷ ⌜hashchain.wish_Proof chainProof
        (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
      "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(serverγ.sig_pk)
        (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
      "#Hwish_hist" ∷ ktcore.wish_ListMemb γ.(serverγ.vrf_pk) uid prevVerLen
        lastDig hist ∗
      "%Heq_hist" ∷ ⌜Forall2
        (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
        (drop (uint.nat prevVerLen) pks) hist⌝ ∗
      "#Hwish_bound" ∷ ktcore.wish_NonMemb γ.(serverγ.vrf_pk) uid
        (W64 $ length pks) lastDig bound
    )) -∗
    Φ #(sl_chainProof, sl_linkSig, sl_hist, ptr_bound, err))) -∗
  WP s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen {{ Φ }}.
Proof.
Admitted.

Lemma wp_Server_Audit s γ (prevEpoch : w64) :
  ∀ Φ,
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ sl_proof (err : ktcore.Blame),
    ((
      "%Herr" ∷ ⌜err = {[ ktcore.BlameUnknown ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.hist)⌝
    ) ∨ (
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
        "#Hwish_linkSig" ∷ ktcore.wish_LinkSig γ.(serverγ.sig_pk)
          (W64 ep) link aud.(ktcore.AuditProof.LinkSig))
      (* no need to explicitly state update labels and vals.
      those are tied down by UpdateProof, which is tied into server's digs.
      dig only commits to one map, which lets auditor know it shares
      same maps as server. *)
    )) -∗
    Φ #(sl_proof, err))) -∗
  WP s @ (ptrT.id server.Server.id) @ "Audit" #prevEpoch {{ Φ }}.
Proof.
Admitted.

Lemma wp_Server_Start s γ :
  ∀ Φ,
  is_Server s γ -∗
  (* read-only. *)
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    ∃ ptr_reply reply last_link,
    "#Hsl_reply" ∷ StartReply.own ptr_reply reply (□) ∗

    "#His_PrevLink" ∷ hashchain.is_chain
      (take (uint.nat reply.(StartReply.PrevEpochLen)) σ.(state.hist).*1)
      None reply.(StartReply.PrevLink)
      (uint.nat reply.(StartReply.PrevEpochLen)) ∗
    "%His_ChainProof" ∷ ⌜hashchain.wish_Proof reply.(StartReply.ChainProof)
      (drop (uint.nat reply.(StartReply.PrevEpochLen)) σ.(state.hist).*1)⌝ ∗
    "#His_last_link" ∷ hashchain.is_chain σ.(state.hist).*1 None
      last_link (length σ.(state.hist)) ∗
    "#His_LinkSig" ∷ ktcore.wish_LinkSig γ.(serverγ.sig_pk)
      (W64 $ length σ.(state.hist) - 1) last_link reply.(StartReply.LinkSig) ∗

    "%Heq_VrfPk" ∷ ⌜γ.(serverγ.vrf_pk) = reply.(StartReply.VrfPk)⌝ ∗
    "#His_VrfSig" ∷ ktcore.wish_VrfSig γ.(serverγ.sig_pk) γ.(serverγ.vrf_pk)
      reply.(StartReply.VrfSig) -∗
    Φ #ptr_reply)) -∗
  WP s @ (ptrT.id server.Server.id) @ "Start" #() {{ Φ }}.
Proof.
Admitted.

(* For proving the "all good clients" idiom spec, perhaps only need an invariant
   like:
inv (∃ σ,
      own_Server γs σ ∗
      ([∗ map] (uid,ver) ↦ pk ∈ σ,
        (witness that uid committed to ver being pk))
) *)

(* For proving the "adversarial clients" idiom spec, perhaps only need an invariant
   like: inv (∃ σ, own_Server γs σ) *)

End proof.
End server.
