From iris.algebra Require Import proofmode_classes.
From iris.base_logic Require Import base_logic.
Set Default Proof Using "Type".

Inductive counting :=
| Count (z: Z)
| CountBot.

Local Open Scope Z.

Instance counting_valid : Valid counting := λ x,
  match x with Count _ => True | CountBot => False end.
Instance counting_validN : ValidN counting := λ n x,
  match x with Count _ => True | CountBot => False end.
Instance counting_pcore : PCore counting := λ x, None.
Instance counting_op : Op counting :=
  λ x y,
  match x, y with
  | Count z1, Count z2 =>
    if (decide (z1 >= 0 ∧ z2 >= 0)) then CountBot else
    if (decide ((z1 >= 0 ∨ z2 >= 0) ∧ (z1 + z2) < 0)) then CountBot else
      Count (z1 + z2)
  | _, _ => CountBot
  end.
Canonical Structure countingC := leibnizO counting.

Local Ltac by_cases :=
  repeat (match goal with
          | [ H: counting |- _ ] => destruct H
          end) => //=;
  repeat destruct decide => //=; try lia.

Lemma counting_ra_mixin : RAMixin counting.
Proof.
  split; try apply _; try done.
  - intros x y z. rewrite /op/counting_op.
    by_cases. f_equal. lia.
  - intros x y. rewrite /op/counting_op.
    by_cases. f_equal. lia.
  - intros x y. rewrite /op/counting_op/valid.
    by_cases.
Qed.

Canonical Structure countingR := discreteR counting counting_ra_mixin.

Global Instance counting_cmra_discrete : CmraDiscrete countingR.
Proof. apply discrete_cmra_discrete. Qed.

Lemma counting_op' (x y : countingR) : (x ⋅ y) = (counting_op x y).
Proof. done. Qed.

Lemma counting_valid' (x : countingR) : ✓ x ↔ (counting_valid x).
Proof. done. Qed.

Lemma counting_validN' n (x : countingR) : ✓{n} x ↔ (counting_validN n x).
Proof. done. Qed.

Global Instance is_op_counting z :
  z >= 0 → IsOp' (Count z) (Count (z + 1)) (Count (-1)).
Proof.
  rewrite /IsOp' /IsOp counting_op' => ?.
  rewrite //=. by_cases. f_equal. lia.
Qed.

Global Instance is_op_counting' (n: nat) :
  IsOp' (Count n) (Count (S n)) (Count (-1)).
Proof.
  rewrite /IsOp' /IsOp counting_op' //=.
  by_cases. f_equal. lia.
Qed.

Global Instance counting_id_free (z : counting) : IdFree z.
Proof.
  intros y.
  rewrite counting_op' counting_validN'.
  by_cases. destruct y; by_cases; intros _; inversion 1.
  lia.
Qed.

Global Instance counting_full_exclusive : Exclusive (Count 0).
Proof.
  intros y. rewrite counting_validN' counting_op'.
  destruct y => //=; by_cases. 
Qed.
