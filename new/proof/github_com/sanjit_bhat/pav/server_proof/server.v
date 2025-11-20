From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

From New.proof Require Import sync time.
From New.proof.github_com.goose_lang Require Import std.
From New.proof.github_com.sanjit_bhat.pav Require Import
  cryptoffi hashchain ktcore merkle.

Module server.

Module state.
Record t :=
  mk {
    (* gmap from uid's to list of pks (indexed by version). *)
    keys: gmap w64 (list $ list w8);
    digs: list $ list w8;
  }.
End state.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.
Context `{!pavG Σ}.

Axiom Server_names : Type.

(* Could put the sigPk into here. *)
Implicit Types γ : Server_names.

Axiom is_Server : ∀ (s : loc) γ, iProp Σ.

Axiom own_Server : ∀ γ (σ : state.t), iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Axiom pure_put : w64 → list w8 → w64 → state.t → state.t.

(* RPC spec needs □ in front of atomic update. *)
Lemma wp_Server_Put s γ uid pk sl_pk ver :
  ∀ Φ,
  is_Server s γ -∗
  sl_pk ↦*□ pk -∗
  □ (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
    (own_Server γ (pure_put uid pk ver σ) ={∅,⊤}=∗
      Φ #())) -∗
  WP s @ (ptrT.id server.Server.id) @ "Put" #uid #sl_pk #ver {{ Φ }}.
Proof.
Admitted.

(* The RPC spec is the same, no □ bc this doesn't mutate σ. *)
(* for idiomatic spec, use GS to contradict BlameUnknown. *)
Lemma wp_Server_History s γ (uid prevEpoch prevVerLen : w64) :
  ∀ Φ,
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗ (own_Server γ σ ={∅,⊤}=∗
    (* postcond. *)
    ∃ (sl_chainProof sl_linkSig sl_hist : slice.t) (ptr_bound : loc) (err : ktcore.Blame),
    ((
      "%Herr" ∷ ⌜err = {[ ktcore.BlameUnknown ]}⌝ ∗
      "%Hwish" ∷ ⌜uint.nat prevEpoch ≥ length σ.(state.digs) ∨
        uint.nat prevVerLen > length (σ.(state.keys) !!! uid)⌝
    ) ∨ (
      ∃ chainProof (linkSig : list w8) sl0_hist hist bound,
      "%Herr" ∷ ⌜err = ∅⌝ ∗

      "#Hsl_chainProof" ∷ sl_chainProof ↦*□ chainProof ∗
      "#Hsl_linkSig" ∷ sl_linkSig ↦*□ linkSig ∗
      "#Hsl_hist" ∷ sl_hist ↦*□ sl0_hist ∗
      "#Hsl0_hist" ∷ ([∗ list] ptr;obj ∈ sl0_hist;hist,
        ktcore.Memb.own ptr obj (□)) ∗
      "#Hptr_bound" ∷ ktcore.NonMemb.own ptr_bound bound (□) ∗

      "%Hwish_chainProof" ∷ ⌜hashchain.wish_Verify chainProof
        (drop (S (uint.nat prevEpoch)) σ.(state.digs))⌝)) -∗
      (* TODO: correctness preds should tie into σ. *)
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
