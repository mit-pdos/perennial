From New.generatedproof.github_com.sanjit_bhat.pav Require Import server.
From New.proof.github_com.sanjit_bhat.pav Require Import prelude.

(*
From New.proof.github_com.sanjit_bhat.pav Require Import
  advrpc auditor cryptoffi hashchain ktcore merkle server sigpred. *)

Module server.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _, !globalsGS Σ} {go_ctx : GoContext}.

Axiom Server_names : Type.

(* Could put the sigPk into here. *)
Implicit Types γ : Server_names.

Axiom is_Server : ∀ (s : loc) γ, iProp Σ.

Definition state := gmap Z Z.

Axiom own_Server : ∀ γ (σ : state), iProp Σ.

Axiom own_Server_timeless : ∀ γ σ,  Timeless (own_Server γ σ).
Global Existing Instance own_Server_timeless.

Axiom pure_put : w64 → list w8 → w64 → state → state.

(* Rpc spec needs □ in front of atomic update. *)
Lemma wp_Server__Put s γ uid pk pk_sl ver :
  ∀ Φ,
  is_Server s γ -∗
  pk_sl ↦* pk -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
        (own_Server γ (pure_put uid pk ver σ) ={∅,⊤}=∗ True)) -∗
  Φ #() -∗
  WP s @ (ptrT.id server.Server.id) @ "Put" #uid #pk_sl #ver {{ Φ }}.
Proof.
Admitted.

Axiom pure_history :
  ∀ (uid prevEpoch prevVerLen : w64) (σ : state), val.
  (* (list w8 * list w8 * list ktcore.Memb.t * ktcore.NonMemb.t * ktcore.Blame.t). *)

Axiom CRYPTO_FACTS : iProp Σ.

(* The RPC spec is the same, no □ because this doesn't mutate σ. *)
Lemma wp_Server__History s γ uid prevEpoch prevVerLen :
  ∀ Φ,
  is_Server s γ -∗
  (|={⊤,∅}=> ∃ σ, own_Server γ σ ∗
        (own_Server γ σ ={∅,⊤}=∗
         CRYPTO_FACTS -∗ Φ (pure_history uid prevEpoch prevVerLen σ))) -∗
  WP s @ (ptrT.id server.Server.id) @ "History" #uid #prevEpoch #prevVerLen {{ Φ }}.
Proof.
Admitted.

End proof.
End server.
