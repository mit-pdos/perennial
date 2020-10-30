Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

Lemma Qp_split_lt (q1 q2: Qp) :
  (q1<q2)%Qp ->
  ∃ q', (q1 + q' = q2)%Qp.
Proof.
  rewrite Qp_lt_sum.
  intros [r EQ]. exists r. done.
Qed.

Lemma Qp_split_1 (q: Qp) :
  (q<1)%Qp ->
  ∃ q', (q + q' = 1)%Qp.
Proof. intros. by eapply Qp_split_lt. Qed.

Theorem Qp_div_2_lt (q: Qp) : (q/2 < q)%Qp.
Proof.
  apply Qp_lt_sum. exists (q/2)%Qp.
  rewrite Qp_div_2. done.
Qed.
