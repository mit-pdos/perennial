From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

Module server.

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

Definition wish_checkMemb pk uid ver dig memb : iProp Σ :=
  ∃ label mapVal,
  let enc_label := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  let enc_val := ktcore.CommitOpen.pure_enc memb.(ktcore.Memb.PkOpen) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc_label memb.(ktcore.Memb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc_label label ∗
  "#His_mapVal" ∷ cryptoffi.is_hash (Some enc_val) mapVal ∗
  "#Hwish_memb" ∷ merkle.wish_VerifyMemb label mapVal memb.(ktcore.Memb.MerkleProof) dig.

Definition wish_checkHist pk uid (prefixLen : w64) dig hist : iProp Σ :=
  ([∗ list] ver ↦ memb ∈ hist,
    wish_checkMemb pk uid (uint.Z prefixLen + ver) dig memb).

Definition wish_checkNonMemb pk uid ver dig nonMemb : iProp Σ :=
  ∃ label,
  let enc := ktcore.MapLabel.pure_enc (ktcore.MapLabel.mk' uid ver) in
  "#His_vrf_proof" ∷ cryptoffi.is_vrf_proof pk enc nonMemb.(ktcore.NonMemb.LabelProof) ∗
  "#His_vrf_out" ∷ cryptoffi.is_vrf_out pk enc label ∗
  "#Hwish_nonMemb" ∷ merkle.wish_VerifyNonMemb label nonMemb.(ktcore.NonMemb.MerkleProof) dig.

Implicit Types γ : serverγ.t.
Implicit Types σ : state.t.

Axiom is_Server : ∀ (s : loc) γ, iProp Σ.

Axiom own_Server : ∀ γ σ, iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Definition pure_put σ uid pk (ver : w64) :=
  let pks := σ.(state.pending) !!! uid in
  (* drops put if not right version. *)
  match bool_decide (uint.nat ver = length pks) with false => σ | _ =>
  set state.pending (<[uid:=pks ++ [pk]]>) σ
  end.

(* RPC spec needs □ in front of atomic update. *)
Lemma wp_Server_Put s γ uid pk sl_pk ver :
  ∀ Φ,
  is_Server s γ -∗
  sl_pk ↦*□ pk -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    (own_Server γ (pure_put σ uid pk ver) ={∅,⊤}=∗ True)) ∗
  Φ #() -∗
  WP s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver {{ Φ }}.
Proof.
Admitted.

(* The RPC spec is the same, no □ bc this doesn't mutate σ. *)
(* for idiomatic spec, use GS to contradict BlameUnknown. *)
Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) :
  ∀ Φ,
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    (* postcond. it only references σ.(state.hist). *)
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
      ∃ chainProof (linkSig : list w8) sl0_hist hist bound,
      "%Herr" ∷ ⌜err = ∅⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch < length σ.(state.hist) ∧
        uint.nat prevVerLen ≤ length pks⌝ ∗

      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ sl_hist ↦*□ sl0_hist ∗
      "#Hsl0_hist" ∷ ([∗ list] ptr;obj ∈ sl0_hist;hist,
        ktcore.Memb.own ptr obj (□)) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "%Hwish_chainProof" ∷ ⌜hashchain.wish_Verify chainProof
        (drop (S (uint.nat prevEpoch)) σ.(state.hist).*1)⌝ ∗
      "#Hwish_linkSig" ∷ ktcore.wish_VerifyLinkSig γ.(serverγ.sig_pk)
        (W64 $ (Z.of_nat numEps - 1)) lastLink linkSig ∗
      "#Hwish_hist" ∷ wish_checkHist γ.(serverγ.vrf_pk) uid prevVerLen
        lastDig hist ∗
      "%Heq_hist" ∷ ⌜Forall2
        (λ x y, x = y.(ktcore.Memb.PkOpen).(ktcore.CommitOpen.Val))
        (drop (uint.nat prevVerLen) pks) hist⌝ ∗
      "#Hwish_bound" ∷ wish_checkNonMemb γ.(serverγ.vrf_pk) uid
        (W64 $ length pks) lastDig bound
    )) -∗
    Φ #(sl_chainProof, sl_linkSig, sl_hist, ptr_bound, err))) -∗
  WP s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen {{ Φ }}.
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
