Require Import Helpers.RelationAlgebra.
Require Import List.

Global Set Implicit Arguments.
Global Generalizable Variables T R Op State.
Global Set Printing Projections.
(* for compatibility with coq master *)
Set Warnings "-undeclared-scope".

Import RelationNotations.

Section Proc.
  Variable Op : Type -> Type.

  Inductive proc : Type -> Type :=
  | Call : forall T (op : Op T), proc T
  | Ret : forall T (v : T), proc T
  | Bind : forall T (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T), proc T
  (* TODO: why is p's argument an option in until? *)
  | Until : forall T (c : T -> bool) (p : option T -> proc T) (v : option T), proc T
  | Spawn : forall T (p: proc T), proc unit.

End Proc.

Arguments Call {Op T}.
Arguments Ret {Op T} v.
Arguments Until {Op T} _ _ _.
Arguments Spawn {Op} _.

(*
Inductive proc_seq (Op: Type -> Type) (R: Type) : Type :=
| Seq_Nil
| Seq_Bind (T : Type) (p : proc Op T) (rx : T + R -> proc_seq Op R).
Arguments Seq_Nil {Op R}.
Arguments Seq_Bind {Op R T}.
*)

(* TODO : allow forwarding the recovery value to the next routine *)
Inductive rec_seq (Op: Type -> Type) : Type :=
| Seq_Nil
| Seq_Cons (T : Type) (p : proc Op T) (ps: rec_seq Op).
Arguments Seq_Nil {Op}.
Arguments Seq_Cons {Op T}.

Fixpoint rec_seq_append Op (ps1 ps2: rec_seq Op) :=
  match ps1 with
  | Seq_Nil => ps2
  | Seq_Cons p ps1' => Seq_Cons p (rec_seq_append ps1' ps2)
  end.

Definition rec_seq_snoc Op T (ps: rec_seq Op) (p: proc Op T) :=
  rec_seq_append ps (Seq_Cons p Seq_Nil).

Definition thread_pool (Op: Type -> Type) := list {T : Type & proc Op T}.

Definition OpSemantics Op State :=
  forall T, Op T -> relation State State T.
Definition CrashSemantics State := relation State State unit.

Record Dynamics Op State :=
  { step: OpSemantics Op State;
    crash_step: CrashSemantics State; }.

Section Dynamics.

  Context `(sem: Dynamics Op State).

  (** First, we define semantics of running programs with halting (without the
  effect of a crash or recovery) *)

  Definition until1 T (c : T -> bool)
                      (p : option T -> proc Op T)
                      (v : option T) :=
    Bind (p v) (fun x => if c x then Ret x else Until c p (Some x)).
   
  Fixpoint exec_step {T} (p: proc Op T)
    : relation State State (proc Op T * thread_pool Op) :=
    match p with
    | Ret v => pure (Ret v, nil)
    | Call op => v <- step sem op; pure (Ret v, nil)
    | @Bind _ T0 _ p p' =>
      vp <- exec_step p;
      (let (p1, t) := vp in
       match p1 in (proc _ T1) return
             (T1 -> proc _ T0) -> relation State State (proc _ T0 * thread_pool _)
       with
        | Ret v => fun p' => pure (p' v, t)
        | p => fun p' => pure (Bind p p',t)
        end) p'
    | Until c p v  => pure (until1 c p v, nil)
    | Spawn T' p' => pure (Ret tt, existT _ T' p' :: nil)
    end.

  (* TODO: need to define this after, otherwise can't use proc in the above *)
  Notation proc := (proc Op).
  Notation rec_seq := (rec_seq Op).
  Notation thread_pool := (thread_pool Op).
  Notation step := sem.(step).
  Notation crash_step := sem.(crash_step).

  Definition exec_pool_hd {T} (p: proc T) (ps: thread_pool)
    : relation State State thread_pool :=
    pps <- exec_step p;
    pure (existT _ T (fst pps) :: ps ++ snd pps).

  Fixpoint exec_pool (ps: list {T & proc T})
    : relation State State thread_pool :=
    match ps with
    | nil => pure nil
    | existT _ T p :: nil => exec_pool_hd p nil
    | existT _ T p :: ps' =>
      (exec_pool_hd p ps') +
      (ps'_upd <- exec_pool ps';
       pure (existT _ T p :: ps'_upd))
    end.

  Definition exec_partial {T} (p: proc T) :=
    bind_star (exec_pool) ((existT _ T p) :: nil).

  Definition exec_halt {T} (p: proc T) : relation State State unit :=
    exec_partial p;; pure tt.

  (* A complete execution is one in which the first thread is a value *)
  Definition exec {T} (p: proc T) : relation State State {T: Type & T} :=
    ps <- exec_partial p;
    match ps with
    | existT _ _ (Ret v) :: _ => pure (existT _ _ v)
    | _ => @none _ _ {T: Type & T}
    end.

  Fixpoint exec_seq_partial (ps: rec_seq) : relation State State unit :=
    match ps with
    | Seq_Nil => pure tt
    | Seq_Cons p ps => (exec p;; exec_seq_partial ps) + (exec_partial p;; pure tt)
    end.

  Fixpoint exec_seq (ps: rec_seq) : relation State State unit :=
    match ps with
    | Seq_Nil => pure tt
    | Seq_Cons p ps => exec p;; exec_seq ps
    end.

  Definition exec_recover1 T (rec: proc T) : relation State State unit :=
    seq_star (exec_partial rec;; crash_step);;
             exec rec;; pure tt.

  Definition exec_recover (rec: rec_seq) : relation State State unit :=
    seq_star (exec_seq_partial rec;; crash_step);;
             exec_seq rec.

  Definition exec_recover_unfold (rec: rec_seq) :
    exec_recover rec =
    (seq_star (exec_seq_partial rec;; crash_step);;
             exec_seq rec) := eq_refl.

  (* recovery execution *)
  Definition rexec {T} (p: proc T) (rec: rec_seq) :=
      exec_partial p;; crash_step;; exec_recover rec.

  Definition rexec_unfold {T} (p: proc T) (rec: rec_seq) :
    rexec p rec =
    (exec_partial p;; crash_step;; exec_recover rec) := eq_refl.

  Definition rexec_seq (ps: rec_seq) (rec: rec_seq) :=
      exec_seq_partial ps;; crash_step;; exec_recover rec.

  Definition rexec_seq_unfold (ps: rec_seq) (rec: rec_seq) :
    rexec_seq ps rec =
    (exec_seq_partial ps;; crash_step;; exec_recover rec) := eq_refl.

  Definition exec_or_rexec {T} (p : proc T) (rec: rec_seq) :=
    (v <- exec p; pure (inl v)) + (v <- rexec p rec; pure (inr v)).

  (* TODO: need to track that the hd type does not change for this to make sense *)
  (*
  Fixpoint exec_seq {R} (p: proc_seq R) (rec: proc R)
    : relation State State (list {X : Type & X}) :=
    match p with
    | Seq_Nil => pure (nil)
    | Seq_Bind p f =>
      v <- exec_or_rexec p rec;
      l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
    end.

  Lemma exec_seq_unfold {R} (p: proc_seq R) (rec: proc R) :
    exec_seq p rec =
    match p with
    | Seq_Nil => pure (nil)
    | Seq_Bind p f =>
      v <- exec_or_rexec p rec;
      l <- exec_seq (f v) rec;
      pure (existT _ _ v :: l)
    end.
  Proof. destruct p; auto. Qed.
   *)

End Dynamics.

Module ProcNotations.
  (* Declare Scope proc_scope. *)
  Delimit Scope proc_scope with proc.
  Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                               (at level 20, p1 at level 100, p2 at level 200, right associativity)
                             : proc_scope.
End ProcNotations.
