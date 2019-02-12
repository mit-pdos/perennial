Require Import Spec.Proc.

Import ProcNotations.
Local Open Scope proc.

Section Programs.
  Variable Op:Type -> Type.
  Notation proc := (Proc.proc Op).

  Definition basic_bind (p1: proc nat) (p2: nat -> proc unit) : proc unit :=
    x <- p1;
      p2 x.

  Definition multiple_bind (p1: proc nat) (p2: nat -> proc unit) : proc unit :=
    x <- p1;
      y <- p1;
      p2 (x+y).

  (* non-canonical association *)
  Definition bind_bind (p1: proc nat) (p2: nat -> proc unit) : proc unit :=
    _ <- x <- p1; p2 x;
      p2 3.

  Definition destructuring_bind (p1: proc (nat*nat)) (p2: nat -> proc unit) : proc unit :=
    let! (x, _) <- p1;
         p2 x.

  Definition unnecessary_destructuring_bind (p1: proc (nat*nat)) (p2: nat -> proc unit) : proc unit :=
    let! x <- p1;
         p2 (fst x).

  Definition destructuring_bind_tuple3 (p1: proc (nat*nat*nat)) (p2: nat -> proc unit) : proc unit :=
    let! (_, x, _) <- p1;
         p2 x.

  Definition destructure_unit (p1: proc unit) (p2: proc unit) : proc unit :=
    let! tt <- p1;
         p2.

End Programs.
