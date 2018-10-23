Require Import Proc.
Require Import Helpers.Instances.
Require Import Helpers.Helpers.

Local Notation "'exec_of!' p" := (exec _ p _ _) (at level 0, only parsing).
Local Notation "'rexec_of!' p" := (rexec _ p _ _ _) (at level 0, only parsing).

Ltac inv_exec :=
  let t H := invertc H in
  repeat match goal with
         | [ H: exec_of! (Ret _) |- _ ] => t H
         | [ H: exec_of! (Bind _ _) |- _ ] => t H
         | [ H: exec_of! (Prim _) |- _ ] => t H
         end.

Ltac inv_rexec :=
  match goal with
  | [ H: rexec_of! _ |- _ ] => invert H
  end.

Section Dynamics.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).
  Notation exec := sem.(exec).
  Notation exec_recover := sem.(exec_recover).
  Notation rexec := sem.(rexec).

  Definition exec_equiv T (p p': proc T) :=
    forall s r, exec p s r <-> exec p' s r.

  Global Instance exec_equiv_equiv T : Equivalence (exec_equiv (T:=T)) :=
    RelInstance.

  Infix "<==>" := exec_equiv (at level 99).

  Hint Constructors Proc.exec.
  Hint Constructors Proc.rexec.

  Theorem monad_left_id T T' (p: T' -> proc T) v :
      Bind (Ret v) p <==> p v.
  Proof.
    split; intros.
    - inv_exec; eauto.
    - eauto.
  Qed.

  Theorem monad_assoc
          `(p1: proc T1)
          `(p2: T1 -> proc T2)
          `(p3: T2 -> proc T3) :
    Bind (Bind p1 p2) p3 <==> Bind p1 (fun v => Bind (p2 v) p3).
  Proof.
    split; intros.
    - inv_exec; eauto.
    - inv_exec; eauto.
  Qed.

  Definition rexec_equiv `(rec: proc R) T (p p': proc T) :=
    forall s r,
      rexec p rec s r <-> rexec p' rec s r.

  Theorem exec_equiv_to_rexec `(rec: proc R) T (p p': proc T) :
    exec_equiv p p' ->
    rexec_equiv rec p p'.
  Proof.
    unfold rexec_equiv; split; intros.
    - inv_rexec.
      apply H in H1; eauto.
      apply H in H1; eauto.
    - inv_rexec.
      apply H in H1; eauto.
      apply H in H1; eauto.
  Qed.

  Instance exec_equiv_to_rexec_subr `(rec: proc R) :
    subrelation (exec_equiv (T:=T)) (rexec_equiv rec (T:=T)).
  Proof.
    unfold subrelation; intros.
    apply exec_equiv_to_rexec; auto.
  Qed.

  Theorem rexec_finish_any_rec
          `(p: proc T)
          `(rec: proc R) `(rec': proc R') :
    forall s v s',
      rexec p rec s (RFinished v s') ->
      rexec p rec' s (RFinished v s').
  Proof.
    intros.
    inv_rexec; eauto.
  Qed.

  (* exec_recover (Bind p p') ==
     (crash_step; exec (Bind p p') -> crash)*;
     crash_step; exec (Bind p p') -> finish ==

     exec_recover p;
     (rexec (p' _) p -> recovered);
     exec (p' _) -> finish
*)

  Theorem exec_recover_bind_inv : forall `(p: proc R)
                                    `(p': R -> proc R')
                                    s rv' s'',
      exec_recover (Bind p p') s rv' s'' ->
      exists rv1 s1, exec_recover p s rv1 s1 /\
                exists rv2 s2,
                  kleene_star
                    (fun '(rv, s) '(rv', s') =>
                       rexec (p' rv) p s (Recovered rv' s'))
                    (rv1, s1) (rv2, s2) /\
                  exec (p' rv2) s2 (Finished rv' s'').
  Proof.
  Admitted.

End Dynamics.
