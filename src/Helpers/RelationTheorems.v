Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.

Import RelationNotations.

Theorem seq_star_invariant A (r: relation A A unit) P :
  test P;; r ---> test P;; r;; test P ->
  test P;; seq_star r ---> test P;; seq_star r;; test P.
Proof.
  intros.
  rewrite <- bind_assoc in H.
  apply simulation_seq in H.
  rewrite H.
  rewrite star_expand; norm.
  apply rel_or_elim_rx; norm.
  - setoid_rewrite <- seq_star_none; norm.
    rewrite test_idem; norm.
  - setoid_rewrite <- seq_star1 at 2; norm.
    setoid_rewrite test_to_id at 2; norm.
Qed.
