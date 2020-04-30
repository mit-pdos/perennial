From stdpp Require Import base.

Ltac solve_inhabited :=
  lazymatch goal with
  | [ |- Inhabited _ ] => apply populate; constructor; apply inhabitant
  end.

Notation "'populate!'" := (ltac:(solve_inhabited)) (at level 0, only parsing).
