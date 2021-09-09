Require Import Qcanon ssreflect.
From stdpp Require Import numbers.
Require Import Psatz.
Require Import QArith.
Local Open Scope Q_scope.

(*
Definition Qp_of_Zp (z : Z) (Hpos : (0 < z)%Z) : Qp.
Proof.
  refine (mk_Qp (Qc_of_Z z) _).
  rewrite -Z2Qc_inj_0.
  rewrite -Z2Qc_inj_lt.
  auto.
Qed.
*)

Definition Qp_of_Z (z : Z) : Qp.
Proof.
  refine (mk_Qp (Qc_of_Z (1 `max` z)) _).
  abstract (rewrite -Z2Qc_inj_0 -Z2Qc_inj_lt; lia).
Defined.

Lemma Qp_of_Z_add (z1 z2 : Z) :
  (0 < z1)%Z →
  (0 < z2)%Z →
  Qp_of_Z (z1 + z2)%Z =
  Qp_add (Qp_of_Z z1) (Qp_of_Z z2).
Proof.
  intros Hpos1 Hpos2.
  rewrite /Qp_of_Z //=.
  apply Qp_to_Qc_inj_iff => //=.
  rewrite -Z2Qc_inj_add.
  f_equal. lia.
Qed.

Fixpoint Qppower (q: Qp) (n: nat) :=
  match n with
  | O => 1%Qp
  | S n' => (q * (Qppower q n'))%Qp
  end.

Lemma Qp_min_glb1_lt (q q1 q2 : Qp) :
  (q < q1 → q < q2 → q < q1 `min` q2)%Qp.
Proof.
  intros Hlt1 Hlt2.
  destruct (Qp_min_spec_le q1 q2) as [(?&->)|(?&->)]; auto.
Qed.

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

Require Import Lqa.
Require Import Lra.
Require Import QArith.
Require Import Reals.

Lemma rhelper1 (q : R) :
  (/ 2 < q)%R →
  (q < 1)%R →
  (1 < q + (1 - q + (q + / 2 - 1) / 2))%R.
Proof. lra. Qed.

Lemma rhelper2 (r : R) :
  (/ 2 < r)%R →
  (r < 1)%R →
  (0 < 1 + - r + (r + / 2 - 1) / 2)%R.
Proof. lra. Qed.

Lemma rhelper3 (r : R) :
  (/ 2 < r)%R →
  (r < 1)%R →
  (0 < / 2 + - (1 + - r + (r + / 2 - 1) / 2))%R.
Proof. lra. Qed.

Lemma R_plus_inv_2_gt_1_split q:
  ((/2  < q)%R → ∃ q1 q2, 0 < q1 ∧ 0 < q2 ∧ (q1 + q2)%R = /2 ∧ 1 < q + q1)%R.
Proof.
  intros Hlt.
  assert (q < 1 ∨ 1 <= q)%R as [Hle|Hgt].
  { lra. }
  - set (q1 := ((1 - q)%R + ((q + /2) - 1)/2)%R).
    set (q2 := (/2 - q1)%R).
    exists q1, q2. split_and!.
    * rewrite /q1. lra.
    * rewrite /q2/q1. lra.
    * assert (1 - q < /2)%R.
      { lra. }
      rewrite /q2/q1.
      lra.
    * rewrite /q1. clear q1 q2. apply rhelper1; auto.
  - exists (/4)%R, (/4)%R.
    split; lra.
Qed.

  Require Import Lqa.

Lemma Q_plus_inv_2_gt_1_split q:
  ((/2  < q)%Q → ∃ q1 q2, 0 < q1 ∧ 0 < q2 ∧ Qred (q1 + q2)%Q = Qred (/2) ∧ 1 < q + q1)%Q.
Proof.
  intros Hlt.
  assert (q < 1 ∨ 1 <= q)%Q as [Hle|Hgt].
  { lra. }
  - set (q1 := ((1 - q)%Q + ((q + /2) - 1)/2)%Q).
    set (q2 := (/2 - q1)%Q).
    exists q1, q2. split_and!.
    * rewrite /q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_0.
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper2.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
    * rewrite /q2/q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_0.
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper3.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
    * apply Qred_complete.
      apply Qreals.eqR_Qeq. rewrite /q2/q1.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as ->.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      generalize (Q2R q). clear.
      intros. field.
    * rewrite /q1.
      apply Qreals.Rlt_Qlt.
      repeat (rewrite ?Qreals.Q2R_plus ?Qreals.Q2R_inv ?Qreals.Q2R_opp
              ?Qreals.Q2R_div ?Qreals.Q2R_minus);
        try (by inversion 1).
      rewrite RMicromega.Q2R_1.
      assert (Q2R 2 = 2%R) as Heq2.
      { replace 2%Q with (1 + 1)%Q by auto.
        rewrite ?Qreals.Q2R_plus.
        rewrite RMicromega.Q2R_1; auto with *. }
      rewrite ?Heq2.
      apply rhelper1.
      { rewrite -Heq2. rewrite -Qreals.Q2R_inv; first by inversion 1.
        apply Qreals.Qlt_Rlt. auto. }
      { rewrite -RMicromega.Q2R_1.
        apply Qreals.Qlt_Rlt. auto. }
  - exists (/4)%Q, (/4)%Q.
    split_and!; try constructor.
    * apply (Qle_lt_trans _ (1 + 0)).
      { eauto with *. }
      rewrite Qplus_comm.
      rewrite (Qplus_comm q).
      apply Qplus_lt_le_compat; auto.
      constructor.
Qed.

Lemma Qp_plus_inv_2_gt_1_split q:
  ((/2  < q)%Qp → ∃ q1 q2, q1 + q2 = /2 ∧ 1 < q + q1)%Qp.
Proof.
  intros. destruct q as (q&Hpos). destruct q as (q&Hcanon).
  edestruct (Q_plus_inv_2_gt_1_split q) as (q1&q2&?&?&?&?).
  { eauto with *. }
  unshelve (eexists _).
  { unshelve (econstructor).
    - apply (Qcanon.Q2Qc q1).
    - apply Qred_lt; auto.
  }
  unshelve (eexists _).
  { unshelve (econstructor).
    - apply (Qcanon.Q2Qc q2).
    - apply Qred_lt; auto.
  }
  rewrite //=.
  split.
  - rewrite /Qp_add//=.
    apply Qp_to_Qc_inj_iff.
    rewrite /Qcanon.Qcplus//=.
    apply Qcanon.Q2Qc_eq_iff.
    transitivity (Qplus' q1 q2).
    { rewrite Qplus'_correct.
      apply Qplus_comp; apply Qred_correct. }
    { rewrite /Qplus'. rewrite H2. constructor. }
  - rewrite /Qcanon.Qclt => //=.
    rewrite ?Qred_correct; auto.
Qed.

Local Open Scope Qp.

Lemma Qp_add_cancel (p q r : Qp) :
  p + q = p + r →
  q = r.
Proof.
  intros Heq.
  apply (anti_symm (≤)%Qp).
  - rewrite (Qp_add_le_mono_l _ _ p). rewrite Heq. eauto.
  - rewrite (Qp_add_le_mono_l _ _ p). rewrite Heq. eauto.
Qed.

Lemma Qp_plus_split_alt (q1 q2 : Qp) :
  ((/2 < q1 < q2) →
  (q2 ≤ 1) →
  ∃ qa qb,
    qa + qa + qb = 1 ∧
    1 < q2 + qa ∧
    q1 ≤ qa + qb)%Qp.
Proof.
  intros Hrange1 Hrange2.
  assert (q1 < 1)%Qp as Hlt1.
  { eapply Qp_lt_le_trans; try eassumption. naive_solver. }
  apply (Qp_split_1) in Hlt1 as (qa&Heq).
  assert (∃ qb, (qa + qa) + qb = 1) as (qb&Heq_qb).
  { apply Qp_split_1.
    cut (qa < /2).
    { intros. rewrite -Qp_inv_half_half. apply Qp_add_lt_mono; auto. }
    apply Qp_lt_nge. intros Hge.
    assert (Hfalse: 1 < q1 + qa).
    { rewrite -Qp_inv_half_half.
      destruct Hrange1 as (Hlt1&Hlt2).
      eapply Qp_lt_le_trans.
      { apply Qp_add_lt_mono_r; (try eassumption). }
      apply Qp_add_le_mono_l. auto. }
    rewrite Heq in Hfalse.
    apply Qp_lt_nge in Hfalse. apply Hfalse. eauto.
  }
  exists qa, qb.
  split_and!; try eauto.
  * rewrite -Heq. apply Qp_add_lt_mono_r. naive_solver.
  * rewrite -Heq in Heq_qb.
    rewrite (comm _ q1 qa) in Heq_qb.
    rewrite -assoc in Heq_qb.
    apply Qp_add_cancel in Heq_qb.
    rewrite -Heq_qb //.
Qed.

Lemma Qp_lt_densely_ordered (q1 q2 : Qp) :
  q1 < q2 →
  ∃ q, (q1 < q < q2).
Proof.
  intros (r&Heq)%Qp_split_lt.
  exists (q1 + (r/2)). split.
  - apply Qp_lt_add_l.
  - rewrite -Heq.
    apply Qp_add_lt_mono_l. apply Qp_div_2_lt.
Qed.
