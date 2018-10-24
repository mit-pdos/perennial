Require Import Spec.Proc.
Require Import Spec.Hoare.

(* define abstraction as transforming a specification in terms of another spec *)
(* TODO: define abstraction in terms of execution, not specs *)
Definition refine_spec AState CState
           (abs: AState -> CState -> Prop)
           A T R
           (spec: Specification A T R AState)
  : Specification (AState*A) T R CState :=
  fun '(s, a) cs =>
    {| pre := abs s cs /\
              (spec a s).(pre);
       post := fun cs' r =>
                 exists s', abs s' cs' /\
                       (spec a s).(post) s' r;
       recovered := fun cs' r =>
                      exists s', abs s' cs' /\
                            (spec a s).(recovered) s' r; |}.
