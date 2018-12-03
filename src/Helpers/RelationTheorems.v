Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.

Import RelationNotations.

Theorem seq_star_invariant A (r: relation A A unit) P :
  (test P;; r) ---> (test P;; r;; test P) ->
  (test P;; seq_star r) ---> (test P;; seq_star r;; test P).
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

Fixpoint seq_rep_n {A T} (n: nat) (p: relation A A T) : relation A A T :=
  match n with
  | O => identity
  | S n' => p ;; seq_rep_n n' p
  end.

Fixpoint bind_rep_n {A T} (n: nat) (p: T -> relation A A T) (o: T) : relation A A T :=
  match n with
  | O => pure o
  | S n' => x <- p o; bind_rep_n n' p x
  end.

Lemma seq_star_inv_rep_n A T (p: relation A A T) a1 a2 t:
  seq_star p a1 a2 t ->
  exists n, seq_rep_n n p a1 a2 t.
Proof.
  induction 1.
  - exists O; firstorder.
  - destruct IHseq_star as (n&?). exists (S n).
    simpl. do 2 eexists; intuition eauto.
Qed.

Lemma bind_star_inv_rep_n A T (p: T -> relation A A T) (o: T) a1 a2 t:
  bind_star p o a1 a2 t ->
  exists n, bind_rep_n n p o a1 a2 t.
Proof.
  induction 1.
  - exists O; firstorder.
  - destruct IHbind_star as (n&?). exists (S n).
    simpl. do 2 eexists; intuition eauto.
Qed.

Lemma seq_star_rep_n_ind {A1 A2 T1 T2} (p: relation A1 A2 T1) q (r: relation A1 A2 T2):
  (forall n, (p ;; seq_rep_n n q) ---> r) ->
  (p ;; seq_star q) ---> r.
Proof.
  intros.
  intros a1 a2 t2 Hl.
  destruct Hl as (t1&a2'&Hp&Hstar).
  eapply seq_star_inv_rep_n in Hstar as (n&?).
  eapply H; do 2 eexists; intuition eauto.
Qed.

Lemma seq_star_alt A T r (x y: A) (t: T):
  seq_star r x y t <-> (exists n, seq_rep_n n r x y t).
Proof.
  split.
  - induction 1.
    * exists O. econstructor.
    * destruct IHseq_star as (n&Hseq).
      exists (S n). econstructor; eauto.
  - intros (n&Hseq). revert x y Hseq.
    induction n; intros x y Hseq.
    * inversion Hseq; subst; econstructor.
    * destruct Hseq as (t'&?&?&?).
      econstructor; eauto.
Qed.

Lemma seq_star_mid_invariant A (p: relation A A unit) (q: relation A A unit) P:
  (test P;; p) ---> (q ;; test P) ->
  (q;; seq_star q) ---> q ->
  (q;; test P;; seq_star p) ---> (q;; test P).
Proof.
  intros Hinv Htrans.
  setoid_rewrite <-bind_assoc.
  apply seq_star_rep_n_ind.
  induction n.
  - simpl. rewrite bind_assoc.
    setoid_rewrite unit_identity.
    setoid_rewrite bind_right_id_unit.
    reflexivity.
  - simpl. setoid_rewrite bind_assoc.
    setoid_rewrite <-bind_assoc at 2.
    setoid_rewrite Hinv.
    setoid_rewrite IHn.
    setoid_rewrite <-bind_assoc.
    setoid_rewrite <-(seq_star1) in Htrans.
    setoid_rewrite <-(seq_star_none) in Htrans.
    setoid_rewrite unit_identity in Htrans.
    setoid_rewrite bind_right_id_unit in Htrans.
    rew Htrans.
Qed.

Lemma any_seq_star_any A T:
  (@any A A T;; seq_star (@any A A T)) ---> any.
Proof.
  eapply seq_star_rep_n_ind.
  induction n; simpl.
  - firstorder.
  - setoid_rewrite IHn.
    apply any_idem.
Qed.