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

Lemma seq_star_any_invariant A (p: relation A A unit) P:
  (test P;; p ---> @any _ _ unit ;; test P) ->
  (@any A _ unit;; test P;; seq_star p ---> @any A _ unit;; test P).
Proof.
  intros Hinv.
  intros a a' [] ([]&amid&Htest&Hstar).
  destruct Hstar as ([]&?&(?&<-)&Hstar).
  induction Hstar; auto.
  { exists tt. eexists; repeat split; eauto. }
  edestruct Hinv as ([]&amid&_&(HP&?)).
  { exists tt. eexists; repeat split; eauto. }
  subst. eapply IHHstar; eauto.
Qed.