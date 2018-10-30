Require Import Spec.Proc.
Require Import Tactical.Propositional.
Require Import Helpers.RelationAlgebra.

Import RelationNotations.

(** Defining specifications, which are just convenient ways to express program
behavior. *)

Record SpecProps T R State :=
  { pre: Prop;
    post: State -> T -> Prop;
    recovered: State -> R -> Prop; }.

Definition Specification A T R State := A -> State -> SpecProps T R State.

Definition spec_exec A T R State (spec: Specification A T R State) :
  relation State State T :=
  fun s s' r => forall a,
    (spec a s).(pre) -> (spec a s).(post) s' r.

Definition spec_rexec A T R State (spec: Specification A T R State) :
  relation State State R :=
  fun s s' r => forall a,
    (spec a s).(pre) -> (spec a s).(recovered) s' r.

Definition spec_impl A A'
           `(spec1: Specification A' T R State)
           `(spec2: Specification A T R State) :=
  forall a s, (spec2 a s).(pre) ->
         exists a', (spec1 a' s).(pre) /\
               (forall s' v, (spec1 a' s).(post) s' v ->
                        (spec2 a s).(post) s' v) /\
               (forall s' rv, (spec1 a' s).(recovered) s' rv ->
                         (spec2 a s).(recovered) s' rv).

Section Hoare.
  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation exec := sem.(exec).
  Notation rexec := sem.(rexec).

  Definition proc_ok A T R
             (p: proc T) (rec: proc R)
             (spec: Specification A T R State) :=
    exec p ---> spec_exec spec /\
    rexec p rec ---> spec_rexec spec.

  Theorem proc_ok_expand A T R
          (p: proc T) (rec: proc R)
          (spec: Specification A T R State) :
    proc_ok p rec spec <->
    forall a s,
      (spec a s).(pre) ->
      (forall s' v, exec p s s' v ->
               (spec a s).(post) s' v) /\
      (forall s' rv, rexec p rec s s' rv ->
                (spec a s).(recovered) s' rv).
  Proof.
    unfold proc_ok, rimpl, spec_exec, spec_rexec; split; intros.
    - intuition eauto 10.
    - split; intros.
      specialize (H a x); intuition eauto.
      specialize (H a x); intuition eauto.
  Qed.

  Theorem spec_impl_relations A A'
          `(spec1: Specification A' T R State)
          `(spec2: Specification A T R State)
          p rec :
    spec_impl spec1 spec2 ->
    proc_ok p rec spec1 ->
    proc_ok p rec spec2.
  Proof.
    unfold spec_impl; intros.
    pose proof (proj1 (proc_ok_expand _ _ _) H0); clear H0.
    apply proc_ok_expand; intros.
    specialize (H a s); propositional.
    specialize (H1 a' s); propositional.
    eauto 10.
  Qed.

End Hoare.
