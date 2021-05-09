From iris.proofmode Require Import base tactics classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.base_logic Require Export lib.ghost_map.
From iris.algebra Require Import excl agree auth gmap csum.

(* Library with resources and invariants to protect resources with an election *)
Section election.

Definition one_shotR V := csumR (exclR unitR) (agreeR (leibnizO V)).

Class electionG Σ := PaxosG {
  election_voteG :> inG Σ fracR;
}.

Context `{!electionG Σ}.
Context `{!invG Σ}.

Definition vote (n_pred:nat) (γ:gname) : iProp Σ :=
  own γ (1/(pos_to_Qp (Pos.of_nat n_pred)))%Qp
.

Definition election_inv (P:iProp Σ) γ : iProp Σ :=
  P
  ∨
  ∃ q, (own γ q%Qp) ∗ ⌜(1/2 < q)%Qp⌝
.

Definition N := nroot .@ "election".

Definition is_election γ P : iProp Σ :=
  inv N (election_inv P γ).

Lemma claim_victory γ P (S:gset nat) n :
  (2*size S) > (n+1) →
  is_election γ P -∗
  ([∗ set] k ∈ S, vote n γ) -∗
  P
.
Proof.
Admitted.

End election.
