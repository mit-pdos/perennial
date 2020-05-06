Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

Lemma Qc_2_nle_1: (2 <= 1)%Qc -> False.
Proof. rewrite /Qcanon.Qcle //= ?Qreduction.Qred_correct. Qed.

Lemma Qp_plus_1_nle_1 (q: Qp): (1%Qp + q <= 1%Qp)%Qc -> False.
Proof.
  apply Qp_not_plus_q_ge_1.
Qed.

Local Lemma Qp_split_1_helper (q: Qp) :
  (q<1)%Qc ->
  ∃ q', (1-q)%Qp = Some q' ∧
        (q' + q = 1)%Qp.
Proof.
  intros Hbound.
  rewrite /Qp_minus /Qp_plus.
  destruct (decide (0 < 1%Qp - q)%Qc); try congruence.
  - eexists; split; first by auto.
    apply Qp_eq; simpl.
    field.
  - exfalso.
    apply n.
    simpl.
    rewrite /Qcminus.
    replace 0%Qc with (q + -q)%Qc by field.
    apply Qcplus_lt_mono_r; auto.
Qed.

Lemma Qp_split_1 (q: Qp) :
  (q<1)%Qc ->
  ∃ q', (q + q' = 1)%Qp.
Proof.
  intros.
  destruct (Qp_split_1_helper q) as [q' [? ?]]; auto.
  exists q'.
  rewrite Qp_plus_comm //.
Qed.

Theorem Qp_div_2_lt (q: Qp) : (q/2 < q)%Qc.
Proof.
  destruct q as [q ?].
  simpl.
  rewrite /Qcdiv.
  replace q with (q * (/2 * 2))%Qc at 2.
  { apply Qcmult_lt_mono_pos_l; auto.
    reflexivity. }
  rewrite Qcmult_inv_l //.
  rewrite Qcanon.Qcmult_1_r //.
Qed.
