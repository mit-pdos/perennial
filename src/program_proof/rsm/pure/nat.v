From iris.proofmode Require Import proofmode.

Definition lt_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, n < x)%nat ns.

Definition le_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, n ≤ x)%nat ns.

Definition gt_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, x < n)%nat ns.

Lemma gt_all_weaken {ns n} n' :
  (n ≤ n')%nat ->
  gt_all n ns ->
  gt_all n' ns.
Proof.
  intros Hge Hgtall x Hx.
  specialize (Hgtall _ Hx). simpl in Hgtall.
  lia.
Qed.

Definition ge_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, x ≤ n)%nat ns.

Definition nz_all (ns : gset nat) :=
  set_Forall (λ x, x ≠ O) ns.

Definition outside_all (ub lb : nat) (ns : gset nat) :=
  set_Forall (λ x, x ≤ ub ∨ lb < x)%nat ns.

Lemma outside_all_weaken_ub {ns ub lb} ub' :
  (ub ≤ ub')%nat ->
  outside_all ub lb ns ->
  outside_all ub' lb ns.
Proof.
  intros Hle Houtside n Hn.
  specialize (Houtside _ Hn).
  destruct Houtside; lia.
Qed.

Lemma outside_all_weaken_lb {ns ub lb} lb' :
  (lb' ≤ lb)%nat ->
  outside_all ub lb ns ->
  outside_all ub lb' ns.
Proof.
  intros Hge Houtside n Hn.
  specialize (Houtside _ Hn).
  destruct Houtside; lia.
Qed.
