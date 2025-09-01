From iris.proofmode Require Import base proofmode classes.
From Perennial.base_logic Require Import lib.own.
From iris.bi.lib Require Import fractional.
From Perennial.program_proof Require Import proof_prelude.
From Perennial.base_logic Require Export lib.ghost_map.
From iris.algebra Require Import excl agree auth gmap csum.

(* Library with resources and invariants to protect resources with an election *)
Section election.

Definition one_shotR V := csumR (exclR unitR) (agreeR (leibnizO V)).

Class electionG Σ := PaxosG {
  #[global] election_voteG :: inG Σ fracR;
}.

Context `{!electionG Σ}.
Context `{!invGS Σ}.

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
  ([∗ set] k ∈ S, vote n γ) ={⊤}=∗
  ▷ P
.
Proof.
  iIntros (?) "#His Hvotes".
  iInv "His" as "Hinner" "Hclose".
  iDestruct "Hinner" as "[Hinner|>Hinner]".
  {
    iFrame "Hinner".
    iMod ("Hclose" with "[Hvotes]").
    {
      iNext.
      iRight.
      admit.
    }
    done.
  }
  {
    iExFalso.
    iDestruct "Hinner" as (q) "[Hinner %Hq]".
    admit.
  }
Admitted.

End election.
