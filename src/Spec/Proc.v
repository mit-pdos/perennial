Require Import Helpers.RelationAlgebra.
Require Import Streams.

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

(** A sequence of procedures that a user might wish to run, where for each
    procedure in the sequence they specify a continuation to run on success,
    and an alternate sequence to run if a crash happens. *)
Inductive proc_seq (Op: Type -> Type) (T : Type) (R: Type) : Type :=
| Seq_Ret (v : T)
| Seq_Bind (T1 : Type) (p1 : proc Op T1) (p2 : T1 -> proc_seq Op T R) (c: R -> proc_seq Op T R).
Arguments Seq_Ret {Op T R}.
Arguments Seq_Bind {Op T R T1}.

Inductive SchedChoice : Set := Crash | Finish.
Definition schedule : Type := Stream SchedChoice.

(** Semantics: defined using big-step execution relations *)

Definition OpSemantics Op State := forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State; }.

Section Dynamics.

  Context `(sem: Dynamics Op State).
  Notation proc := (proc Op).
  Notation proc_seq := (proc_seq Op).
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

  Fixpoint exec_seq {T R} (p: proc_seq T R) (rec: proc R) (s: schedule)
    : relation State State T :=
    match p with
    | Seq_Ret v => pure v
    | Seq_Bind p1 f c =>
      match s with
      | Cons b s' =>
        match b with
        | Crash => r <- rexec p1 rec; exec_seq (c r) rec s'
        | Finish => v <- exec p1; exec_seq (f v) rec s'
        end
      end
    end.

  Lemma exec_seq_unfold {T R} (p: proc_seq T R) (rec: proc R) s :
    exec_seq p rec s =
      match p with
      | Seq_Ret v => pure v
      | Seq_Bind p1 f c =>
        match s with
        | Cons b s' =>
          match b with
          | Crash => r <- rexec p1 rec; exec_seq (c r) rec s'
          | Finish => v <- exec p1; exec_seq (f v) rec s'
          end
        end
      end.
  Proof. destruct p; auto. Qed.

End Dynamics.

Module ProcNotations.
  Declare Scope proc_scope.
  Delimit Scope proc_scope with proc.
  Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                               (at level 54, right associativity) : proc_scope.
End ProcNotations.
