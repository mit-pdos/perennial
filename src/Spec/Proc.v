Require Import Helpers.RelationAlgebra.

Global Set Implicit Arguments.
Global Generalizable Variables T R Op State.
Global Set Printing Projections.

Import RelationNotations.

(** Syntax: free monad over a type family of operations *)
Inductive proc (Op: Type -> Type) (T : Type) : Type :=
| Prim (op : Op T)
| Ret (v : T)
| Bind (T1 : Type) (p1 : proc Op T1) (p2 : T1 -> proc Op T).
Arguments Prim {Op T}.
Arguments Ret {Op T} v.

(** Semantics: defined using big-step execution relations *)

Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State; }.

Section Dynamics.

  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).

  (** First, we define semantics of running programs with halting (without the
  effect of a crash or recovery) *)

  Fixpoint exec {T} (p: proc T) : relation State State T :=
    match p with
    | Ret v => pure v
    | Prim op => step op
    | Bind p p' => v <- exec p; exec (p' v)
    end.

  Fixpoint exec_crash {T} (p: proc T) : relation State State unit :=
    match p with
    | Ret v => pure tt
    | Prim op => pure tt + (step op;; pure tt)
    | Bind p p' => pure tt +
                  exec_crash p +
                  (v <- exec p;
                     exec_crash (p' v))
    end.

  Definition exec_recover {R} (rec: proc R) : relation State State R :=
    seq_star (exec_crash rec;; crash_step);;
             exec rec.

  Definition exec_recover_unfold {R} (rec: proc R) :
    exec_recover rec =
    seq_star (exec_crash rec;; crash_step);;
             exec rec := eq_refl.

  (* recovery execution *)
  Definition rexec {T R} (p: proc T) (rec: proc R) : relation State State R :=
      exec_crash p;; crash_step;; exec_recover rec.

  Definition rexec_unfold {T R} (p: proc T) (rec: proc R) :
    rexec p rec =
    exec_crash p;; crash_step;; exec_recover rec := eq_refl.

End Dynamics.

Module ProcNotations.
  Declare Scope proc_scope.
  Delimit Scope proc_scope with proc.
  Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                               (at level 54, right associativity) : proc_scope.
End ProcNotations.
