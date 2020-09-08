Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

Definition Qmin (q1 q2: Q) : Q :=
  match Qlt_le_dec q1 q2 with
  | left _ => q1
  | _ => q2
  end.

Lemma Qmin_glb_r p q1 q2 :
  (p <= Qmin q1 q2 → p <= q2).
Proof.
  rewrite /Qmin. destruct Qlt_le_dec; eauto.
  intros.
  eapply Qle_trans; first eassumption.
  rewrite Qle_lteq. eauto.
Qed.

Lemma Qmin_glb_l p q1 q2 :
  (p <= Qmin q1 q2 → p <= q1).
Proof.
  rewrite /Qmin. destruct Qlt_le_dec; eauto.
  intros. eapply Qle_trans; first eassumption.
  auto.
Qed.

Definition Qcmin (q1 q2: Qc) : Qc.
  refine {| this := Qmin q1 q2; canon := _|}.
  abstract (rewrite /Qmin; destruct Qlt_le_dec; apply canon).
Defined.

Definition Qpmin (q1 q2: Qp) : Qp.
  refine {| Qp_car := Qcmin q1 q2; Qp_prf := _|}.
  abstract (rewrite /Qcmin/Qmin/Qclt/=; destruct Qlt_le_dec; apply Qp_prf).
Defined.

Lemma Qc_2_nle_1: (2 <= 1)%Qc -> False.
Proof. rewrite /Qcanon.Qcle //= ?Qreduction.Qred_correct. Qed.

Lemma Qp_plus_1_nle_1 (q: Qp): (1%Qp + q <= 1%Qp)%Qc -> False.
Proof.
  apply Qp_not_plus_q_ge_1.
Qed.

Local Lemma Qp_split_lt_helper (q: Qp) (c: Qp):
  (q<c)%Qc ->
  ∃ q', (c-q)%Qp = Some q' ∧
        (q' + q = c)%Qp.
Proof.
  intros Hbound.
  rewrite /Qp_minus /Qp_plus.
  destruct (decide (0 < c%Qp - q)%Qc); try congruence.
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

Lemma Qp_split_lt (q1 q2: Qp) :
  (q1<q2)%Qc ->
  ∃ q', (q1 + q' = q2)%Qp.
Proof.
  intros.
  destruct (Qp_split_lt_helper q1 q2) as [q' [? ?]]; auto.
  exists q'.
  rewrite Qp_plus_comm //.
Qed.

Lemma Qp_split_1 (q: Qp) :
  (q<1)%Qc ->
  ∃ q', (q + q' = 1)%Qp.
Proof. intros. by eapply Qp_split_lt. Qed.

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

Theorem Qp_weaken_common (q1 q2: Qp) :
  (∃ qmin q1rest q2rest,
    q1 = qmin + q1rest ∧
    q2 = qmin + q2rest)%Qp.
Proof.
  set (qmin := ((Qpmin q1 q2)/2)%Qp).
  assert (qmin < q1)%Qc.
  { eapply Qlt_le_trans; first eapply Qp_div_2_lt.
    eapply Qmin_glb_l; apply Qle_refl. }
  assert (qmin < q2)%Qc.
  { eapply Qlt_le_trans; first eapply Qp_div_2_lt.
    eapply Qmin_glb_r; apply Qle_refl. }
  edestruct (Qp_split_lt qmin q1) as (q1rest&?); auto.
  edestruct (Qp_split_lt qmin q2) as (q2rest&?); auto.
  exists qmin, q1rest, q2rest; eauto.
Qed.
