Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationTheorems.
Require Import List.

Global Set Implicit Arguments.
Global Generalizable All Variables.
Global Set Printing Projections.
(* for compatibility with coq master *)
Set Warnings "-undeclared-scope".

Import RelationNotations.

Definition Event : Type := {T: Type & T}.

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
Arguments Err {_ _}.

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
    | nil => none
    | existT _ T p :: ps' =>
      (exec_pool_hd p ps') +
      (ps'_upd <- exec_pool ps';
       pure (existT _ T p :: ps'_upd))
    (* Redundant *)
    (* | existT _ T p :: nil => exec_pool_hd p nil *)
    end.

  Inductive exec_pool_alt (ps1: thread_pool) (σ1: State) (ret: Return State thread_pool) : Prop :=
    | step_atomic_valid {T} (e1 e2: proc T) ps2 efs σ2 t1 t2 :
       ps1 = t1 ++ existT _ _ e1 :: t2 ->
       ps2 = t1 ++ existT _ _ e2 :: t2 ++ efs ->
       ret = Val σ2 ps2 ->
       exec_step e1 σ1 (Val σ2 (e2, efs)) ->
       exec_pool_alt ps1 σ1 ret
    | step_atomic_error {T} (e1: proc T) t1 t2 :
       ps1 = t1 ++ existT _ _ e1 :: t2 ->
       ret = Err ->
       exec_step e1 σ1 Err ->
       exec_pool_alt ps1 σ1 ret.

  Lemma exec_pool_alt_cons_valid {T} ps1 σ1 σ2 ps2 e:
    exec_pool_alt ps1 σ1 (Val σ2 ps2) ->
    exec_pool_alt (existT _ T e :: ps1) σ1 (Val σ2 (existT _ T e :: ps2)).
  Proof.
    inversion 1; [| congruence].
    subst. inversion H2; subst; econstructor; eauto;
    rewrite app_comm_cons; f_equal.
  Qed.

  Lemma exec_pool_alt_cons_err {T} ps1 σ1 e:
    exec_pool_alt ps1 σ1 Err ->
    exec_pool_alt (existT _ T e :: ps1) σ1 Err.
  Proof.
    inversion 1; [congruence|].
    subst. subst; econstructor; eauto;
    rewrite app_comm_cons; f_equal.
  Qed.

  Lemma exec_pool_equiv_alt_val ps1 σ1 σ2 ps2:
    exec_pool ps1 σ1 (Val σ2 ps2) <-> exec_pool_alt ps1 σ1 (Val σ2 ps2).
  Proof.
    split.
    - revert σ2 ps2. induction ps1 as [|[T e] ps1]; intros σ2 ps2.
      * simpl. inversion 1.
      * simpl.
          intros [H|H].
          ** destruct H as ((e'&efs)&?&?&Hp).
             inversion Hp; subst.
             eapply (step_atomic_valid _ e e' efs nil ps1); simpl; eauto.
          ** inversion H as (ps2'&?&?&Hpure). inversion Hpure; subst.
             eapply exec_pool_alt_cons_valid; eauto.
    - inversion 1; subst. clear H. inversion_clear H2; subst.
      induction t1 as [|[T' e] ps1].
      * simpl. left.
        do 2 econstructor; split; eauto.
        econstructor.
      * simpl. right.
           do 2 eexists; split; eauto.
           econstructor; eauto.
      * congruence.
  Qed.

  Lemma exec_pool_equiv_alt_err ps1 σ1:
    exec_pool ps1 σ1 Err <-> exec_pool_alt ps1 σ1 Err.
  Proof.
    split.
    - induction ps1 as [|[T e] ps1]. 
      * simpl. inversion 1.
      * simpl. 
        {
          intros [H|H].
           ** destruct H as [?|(?&?&?&Hpure)].
              eapply (step_atomic_error _ e nil ps1); simpl; eauto.
              inversion Hpure.
           ** apply bind_pure_no_err in H.
              eapply exec_pool_alt_cons_err; eauto.
        }
    - inversion 1; subst; clear H;
      induction t1 as [|[T' e] ps1].
      * congruence.
      * congruence. 
      * simpl. left. left. eauto.
      * simpl. right. left. intuition eauto.
  Qed.

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

  Definition exec_recover_partial (rec: rec_seq) : relation State State unit :=
    seq_star (exec_seq_partial rec;; crash_step);;
             exec_seq_partial rec.

  Definition exec_recover_unfold (rec: rec_seq) :
    exec_recover rec =
    (seq_star (exec_seq_partial rec;; crash_step);;
             exec_seq rec) := eq_refl.

  Definition exec_recover_partial_unfold (rec: rec_seq) :
    exec_recover_partial rec =
    (seq_star (exec_seq_partial rec;; crash_step);;
             exec_seq_partial rec) := eq_refl.

  (* recovery execution *)
  Definition rexec {T} (p: proc T) (rec: rec_seq) :=
    exec_partial p;; crash_step;; exec_recover rec.

  Definition rexec_unfold {T} (p: proc T) (rec: rec_seq) :
    rexec p rec =
    (exec_partial p;; crash_step;; exec_recover rec) := eq_refl.

  Definition rexec_partial {T} (p: proc T) (rec: rec_seq) :=
    exec_partial p;; crash_step;; exec_recover_partial rec.

  Definition rexec_seq (ps: rec_seq) (rec: rec_seq) :=
      exec_seq_partial ps;; crash_step;; exec_recover rec.

  Definition rexec_seq_partial (ps: rec_seq) (rec: rec_seq) :=
      exec_seq_partial ps;; crash_step;; exec_recover_partial rec.

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

(* replacements for Until loops *)

Definition DoWhile Op T (body: T -> proc Op (option T)) (init: T) : proc Op T :=
  Bind (Until (T:=option T * T) (fun '(v, last) => match v with
               | Some _ => false
               | None => true
               end)
        (fun v => match v with
               | Some (Some x, last) => Bind (body x) (fun v => Ret (v, x))
               | Some (None, last) => Ret (None, last)
               | None => Ret (None, init)
               end)
        (Some (Some init, init)))
       (fun '(_, last) => Ret last).

Definition DoWhileVoid Op T (body: T -> proc Op (option T)) (init: T) : proc Op unit :=
  Bind (Until (T:=option T) (fun v => match v with
               | Some _ => false
               | None => true
               end)
        (fun v => match v with
               | Some (Some x) => body x
               | Some None => Ret None
               | None => Ret None
               end)
        (Some (Some init)))
       (fun _ => Ret tt).

Inductive LoopOutcome (T R:Type) : Type :=
| ContinueOutcome (x:T)
| DoneWithOutcome (r:R).

Definition Continue {Op T R} (x:T) : proc Op (LoopOutcome T R) := Ret (ContinueOutcome R x).
Definition LoopRet {Op T R} (x:R) : proc Op (LoopOutcome T R) := Ret (DoneWithOutcome T x).

(* TODO: define all loops in terms of this more flexible version *)
Definition Loop Op T R (body: T -> proc Op (LoopOutcome T R)) (init:T) : proc Op R.
Admitted.
