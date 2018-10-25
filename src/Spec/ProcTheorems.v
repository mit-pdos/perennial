Require Import Proc.
Require Import Tactical.ProofAutomation.
Require Import Helpers.Instances.
Require Import Helpers.RelationAlgebra.

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

  Theorem exec_to_crash T (p: proc T) :
    exec p;; pure tt ---> exec_crash p.
  Proof.
    induction p; simpl in *; norm.
    - rewrite <- rel_or_intror.
      reflexivity.
    - setoid_rewrite H.
      rewrite <- rel_or_intror.
      eauto.
  Qed.

  Theorem exec_crash_noop T (p: proc T) :
    pure tt ---> exec_crash p.
  Proof.
    induction p; simpl in *; norm.
    - rewrite <- rel_or_introl; auto.
    - rewrite <- rel_or_introl, <- rel_or_introl; auto.
  Qed.

  Theorem exec_crash_ret T (v: T) :
    exec_crash (Ret v) <---> pure tt.
  Proof.
    reflexivity.
  Qed.

  Theorem exec_crash_idem T (p: proc T) :
    pure tt + exec_crash p <---> exec_crash p.
  Proof.
    apply rimpl_or; auto using exec_crash_noop.
  Qed.

  Definition exec_equiv T (p p': proc T) :=
    requiv (exec p) (exec p').

  Global Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)) :=
    RelInstance.

  Infix "<==>" := exec_equiv (at level 99).

  Theorem monad_left_id T T' (p: T' -> proc T) v :
      Bind (Ret v) p <==> p v.
  Proof.
    unfold "<==>"; simpl; norm.
  Qed.

  Theorem monad_assoc
          `(p1: proc T1)
          `(p2: T1 -> proc T2)
          `(p3: T2 -> proc T3) :
    Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
  Proof.
    unfold "<==>"; simpl; norm.
  Qed.

  Theorem exec_recover_bind
          `(rec1: proc R)
          `(rec2: R -> proc R') :
    exec_recover (Bind rec1 rec2) --->
                 (v <- exec_recover rec1;
                    v' <- bind_star (fun v => rexec (rec2 v) rec1) v;
                    exec (rec2 v')).
  Proof.
    repeat unfold exec_recover, rexec; simpl; norm.
    rewrite exec_crash_idem.
    rewrite ?bind_dist_r; norm.

    (* a few abstractions *)
    gen (exec rec1) (exec_crash rec1) crash_step;
      clear rec1;
      intros rec1 rec1_crash crash.

    rewrite denesting; norm.
    rel_congruence.

    rewrite <- ?bind_assoc.
    rel_congruence; norm.

    rewrite bind_sliding; norm.
  Qed.

End Dynamics.
