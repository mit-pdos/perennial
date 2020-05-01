Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

Lemma Qc_2_nle_1: (2 <= 1)%Qc -> False.
Proof. rewrite /Qcanon.Qcle //= ?Qreduction.Qred_correct. Qed.

Lemma Qp_plus_1_nle_1 (q: Qp): (1%Qp + q <= 1%Qp)%Qc -> False.
Proof.
  rewrite -(Qcanon.Qcplus_0_r Qp_one) /Qcanon.Qcle //= ?Qreduction.Qred_correct.
  assert (QArith_base.Qlt 0 (Qcanon.this q)).
  { destruct q. simpl in *. eauto. }
  nra.
Qed.
