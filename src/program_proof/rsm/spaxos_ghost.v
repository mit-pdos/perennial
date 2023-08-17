(**
 * Ghost state definitions, type class instances, and rules.
 *)
From Perennial.program_proof Require Import spaxos_top.
From Perennial.base_logic Require Import ghost_map mono_nat.
From iris.algebra Require Import mono_nat mono_list gmap_view gset.

Inductive consensus : Set :=
| Chosen (v : string)
| Free.

Class spaxos_ghostG (Σ : gFunctors).

Record spaxos_names := {}.

Section consensus.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition is_chosen γ (v : string) : iProp Σ.
  Admitted.

  Definition own_free γ : iProp Σ.
  Admitted.

  (* Type class instances. *)
  Instance is_chosen_persistent γ :
    Persistent (∀ v, is_chosen γ v).
  Admitted.
  
  (* Rules. *)
  Lemma consensus_update {γ} v :
    own_free γ ==∗
    is_chosen γ v.
  Admitted.

  Lemma consensus_agree {γ} v1 v2 :
    is_chosen γ v1 -∗
    is_chosen γ v2 -∗
    ⌜v1 = v2⌝.
  Admitted.
End consensus.

Section proposal.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition is_proposal γ (n : nat) (v : string) : iProp Σ.
  Admitted.

  Definition own_proposals γ (ps : gmap nat string) : iProp Σ.
  Admitted.
  
  (* Type class instances. *)
  Instance is_proposal_persistent γ :
    Persistent (∀ n v, is_proposal γ n v).
  Admitted.

  (* Rules. *)
  Lemma proposals_insert {γ} ps n v :
    ps !! n = None ->
    own_proposals γ ps ==∗
    own_proposals γ (<[n := v]> ps) ∗ is_proposal γ n v.
  Admitted.
End proposal.

Section ballot.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition own_ballot γ (x : nat) (b : ballot) : iProp Σ.
  Admitted.

  Definition is_ballot_lb γ (x : nat) (b : ballot) : iProp Σ.
  Admitted.

  Definition own_ballots γ (bs : gmap nat ballot) : iProp Σ.
  Admitted.

  (* Type class instances. *)
  Instance is_ballot_lb_persistent γ :
    Persistent (∀ x b, is_ballot_lb γ x b).
  Admitted.

  (* Rules. *)
  Lemma ballot_update {γ} bs x b b' :
    prefix b b' ->
    own_ballot γ x b -∗
    own_ballots γ bs ==∗
    own_ballot γ x b' ∗ own_ballots γ (<[x := b']> bs).
  Admitted.
End ballot.
