Require Import Proc.
Require Import Helpers.Instances.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.Helpers.

Import RelationNotations.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).
  Notation exec_crash := sem.(exec_crash).
  Notation exec := sem.(exec).
  Notation exec_recover := sem.(exec_recover).
  Notation rexec := sem.(rexec).

  Hint Resolve rimpl_refl requiv_refl.

  Ltac monad :=
    rewrite ?bind_assoc, ?bind_left_id;
    repeat (setoid_rewrite bind_assoc ||
            setoid_rewrite bind_left_id);
    try reflexivity.

  Theorem exec_to_crash T (p: proc T) :
    rimpl (exec p;; pure tt) (exec_crash p).
  Proof.
    induction p; simpl in *; monad.
    - rewrite <- rel_or_intror.
      reflexivity.
    - setoid_rewrite H.
      rewrite <- rel_or_intror.
      eauto.
  Qed.

  Definition exec_equiv T (p p': proc T) :=
    requiv (exec p) (exec p').

  Global Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)) :=
    RelInstance.

  Infix "<==>" := exec_equiv (at level 99).

  Theorem monad_left_id T T' (p: T' -> proc T) v :
      Bind (Ret v) p <==> p v.
  Proof.
    unfold "<==>"; simpl; monad.
  Qed.

  Theorem monad_assoc
          `(p1: proc T1)
          `(p2: T1 -> proc T2)
          `(p3: T2 -> proc T3) :
    Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
  Proof.
    unfold "<==>"; simpl; monad.
  Qed.

  Theorem exec_recover_bind_inv
          `(rec1: proc R)
          `(rec2: R -> proc R') :
    exec_recover (Bind rec1 rec2) --->
                 (v <- exec_recover rec1;
                    v' <- bind_star (fun v => rexec (rec2 v) rec1) v;
                    exec (rec2 v')).
  Proof.
    repeat unfold exec_recover, rexec; simpl; monad.
    rewrite ?bind_dist_r; monad.
  Admitted.

End Dynamics.
