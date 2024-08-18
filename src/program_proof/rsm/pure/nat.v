From iris.proofmode Require Import proofmode.

Definition lt_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, n < x)%nat ns.

Definition le_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, n ≤ x)%nat ns.

Definition gt_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, x < n)%nat ns.

Definition ge_all (n : nat) (ns : gset nat) :=
  set_Forall (λ x, x ≤ n)%nat ns.

Definition nz_all (ns : gset nat) :=
  set_Forall (λ x, x ≠ O) ns.

Definition outside_all (ub lb : nat) (ns : gset nat) :=
  set_Forall (λ x, x ≤ ub ∨ lb < x)%nat ns.
