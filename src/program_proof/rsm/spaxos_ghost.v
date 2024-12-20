(**
 * Ghost state definitions, type class instances, and rules.
 *)
From Perennial.program_proof Require Import spaxos_top.
From Perennial.base_logic Require Import ghost_map mono_nat.
From iris.algebra Require Import mono_nat mono_list gmap_view gset.

Class spaxos_ghostG (Σ : gFunctors).

Record spaxos_names := {}.

Section consensus.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition own_consensus γ (c : consensus) : iProp Σ.
  Admitted.

  Definition own_consensus_half γ (c : consensus) : iProp Σ.
  Admitted.

  Definition is_chosen_consensus γ v : iProp Σ :=
    own_consensus_half γ (Chosen v).

  Definition own_candidates γ (vs : gset byte_string) : iProp Σ.
  Admitted.

  Definition own_candidates_half γ (vs : gset byte_string) : iProp Σ.
  Admitted.

  (* Type class instances. *)
  #[global]
  Instance is_chosen_consensus_persistent γ v :
    Persistent (is_chosen_consensus γ v).
  Admitted.
  
  (* Rules. *)
  Lemma consensus_update {γ} v vs :
    v ∈ vs ->
    own_consensus γ Free -∗
    own_candidates_half γ vs ==∗
    own_consensus γ (Chosen v) ∗ own_candidates_half γ vs.
  Admitted.

  Lemma consensus_witness {γ v} :
    own_consensus_half γ (Chosen v) -∗
    is_chosen_consensus γ v.
  Admitted.

  Lemma consensus_combine {γ v1 v2} :
    own_consensus_half γ v1 -∗
    own_consensus_half γ v2 -∗
    own_consensus γ v1 ∧ ⌜v1 = v2⌝.
  Admitted.

  Lemma consensus_split {γ v} :
    own_consensus γ v -∗
    own_consensus_half γ v ∗ own_consensus_half γ v.
  Admitted.

  Lemma consensus_agree {γ v1 v2} :
    is_chosen_consensus γ v1 -∗
    is_chosen_consensus γ v2 -∗
    ⌜v1 = v2⌝.
  Admitted.

  Lemma candidates_update {γ vs1} vs2 :
    vs1 ⊆ vs2 ->
    own_candidates γ vs1 ==∗
    own_candidates γ vs2.
  Admitted.

  Lemma candidates_combine {γ vs1 vs2} :
    own_candidates_half γ vs1 -∗
    own_candidates_half γ vs2 -∗
    own_candidates γ vs1 ∧ ⌜vs1 = vs2⌝.
  Admitted.

  Lemma candidates_split {γ vs} :
    own_candidates γ vs -∗
    own_candidates_half γ vs ∗ own_candidates_half γ vs.
  Admitted.

  Lemma consensus_incl {γ v vs} :
    own_consensus_half γ (Chosen v) -∗
    own_candidates_half γ vs -∗
    ⌜v ∈ vs⌝.
  Admitted.
End consensus.

Section commitment.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition own_commitment γ (c : consensus) : iProp Σ.
  Admitted.

  Definition is_chosen_commitment γ v : iProp Σ :=
    own_commitment γ (Chosen v).

  (* Type class instances. *)
  #[global]
  Instance is_chosen_commitment_persistent γ v :
    Persistent (is_chosen_commitment γ v).
  Admitted.

  (* Rules. *)
  Lemma commitment_update {γ} v :
    own_commitment γ Free ==∗
    own_commitment γ (Chosen v).
  Admitted.

  Lemma commitment_witness {γ v} :
    own_commitment γ (Chosen v) -∗
    is_chosen_commitment γ v.
  Admitted.

  Lemma commitment_agree {γ v1 v2} :
    is_chosen_commitment γ v1 -∗
    is_chosen_commitment γ v2 -∗
    ⌜v1 = v2⌝.
  Admitted.

  Lemma commitment_discharged {γ} c v :
    own_commitment γ c -∗
    is_chosen_commitment γ v -∗
    ⌜c = Chosen v⌝.
  Admitted.
End commitment.

Section proposal.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition is_proposal γ (n : nat) (v : byte_string) : iProp Σ.
  Admitted.

  Definition own_proposals γ (ps : gmap nat byte_string) : iProp Σ.
  Admitted.
  
  (* Type class instances. *)
  #[global]
  Instance is_proposal_persistent γ n v :
    Persistent (is_proposal γ n v).
  Admitted.

  (* Rules. *)
  Lemma proposals_insert {γ} ps n v :
    ps !! n = None ->
    own_proposals γ ps ==∗
    own_proposals γ (<[n := v]> ps) ∗ is_proposal γ n v.
  Admitted.

  Lemma proposal_lookup {γ} ps n v :
    is_proposal γ n v -∗
    own_proposals γ ps -∗
    ⌜ps !! n = Some v⌝.
  Admitted.
End proposal.

Section ballot.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition own_ballot γ (x : u64) (b : ballot) : iProp Σ.
  Admitted.

  Definition is_ballot_lb γ (x : u64) (b : ballot) : iProp Σ.
  Admitted.

  Definition own_ballots γ (bs : gmap u64 ballot) : iProp Σ.
  Admitted.

  (* Type class instances. *)
  #[global]
  Instance is_ballot_lb_persistent γ x b :
    Persistent (is_ballot_lb γ x b).
  Admitted.

  (* Rules. *)
  Lemma ballot_lookup {γ bs x b} :
    own_ballot γ x b -∗
    own_ballots γ bs -∗
    ⌜bs !! x = Some b⌝.
  Admitted.

  Lemma ballot_update {γ bs x b} b' :
    prefix b b' ->
    own_ballot γ x b -∗
    own_ballots γ bs ==∗
    own_ballot γ x b' ∗ own_ballots γ (<[x := b']> bs).
  Admitted.

  Lemma ballot_witness {γ x b} :
    own_ballot γ x b -∗
    is_ballot_lb γ x b.
  Admitted.

  Lemma ballots_prefix {γ} bs bsqlb :
    ([∗ map] x ↦ b ∈ bsqlb, is_ballot_lb γ x b) -∗
    own_ballots γ bs -∗
    ⌜dom bsqlb ⊆ dom bs ∧ prefixes bsqlb bs⌝.
  Admitted.
End ballot.

Section term.
  Context `{!spaxos_ghostG Σ}.
  (* TODO: remove this once we have real defintions for resources. *)
  Implicit Type (γ : spaxos_names).

  (* Definitions. *)
  Definition own_terms γ (ts : gmap u64 nat) : iProp Σ.
  Admitted.

  Definition own_term γ (x : u64) (n : nat) : iProp Σ.
  Admitted.

  (* Rules. *)
  Lemma term_lookup {γ ts x n} :
    own_term γ x n -∗
    own_terms γ ts -∗
    ⌜ts !! x = Some n⌝.
  Admitted.

  Lemma term_update {γ ts x n} n' :
    own_term γ x n -∗
    own_terms γ ts ==∗
    own_term γ x n' ∗ own_terms γ (<[x := n']> ts).
  Admitted.
End term.
