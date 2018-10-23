Require Import Proc.
Require Import Helpers.Instances.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.Helpers.

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

  Theorem exec_to_crash T (p: proc T) :
    rimpl (exec p;; pure tt) (exec_crash p).
  Proof.
    induction p; simpl in *.
    - rewrite <- rel_or_intror.
      reflexivity.
    - rewrite seq_left_id.
      reflexivity.
    - rewrite <- rel_or_intror.
      rewrite <- rel_or_intror.
      rewrite bind_seq_assoc.
      apply and_then_cong; auto.
  Qed.

  Definition exec_equiv T (p p': proc T) :=
    requiv (exec p) (exec p').

  Global Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)) :=
    RelInstance.

  Infix "<==>" := exec_equiv (at level 99).

  Theorem monad_left_id T T' (p: T' -> proc T) v :
      Bind (Ret v) p <==> p v.
  Proof.
    unfold "<==>"; simpl.
    rewrite bind_left_id; auto.
  Qed.

  Theorem monad_assoc
          `(p1: proc T1)
          `(p2: T1 -> proc T2)
          `(p3: T2 -> proc T3) :
    Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
  Proof.
    unfold "<==>"; simpl.
    rewrite bind_assoc; auto.
  Qed.

  (* exec_recover (Bind p p') ==
     (crash_step; exec (Bind p p') -> crash)*;
     crash_step; exec (Bind p p') -> finish ==

     exec_recover p;
     (rexec (p' _) p -> recovered);
     exec (p' _) -> finish
*)

End Dynamics.
