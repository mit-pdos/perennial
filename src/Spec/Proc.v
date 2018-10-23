Global Set Implicit Arguments.
Global Generalizable Variables T Op State.
Global Set Printing Projections.

Section Proc.

  (** Syntax: free monad over a type family of operations *)

  Context (Op:Type -> Type).

  Inductive proc (T : Type) : Type :=
  | Prim (op : Op T)
  | Ret (v : T)
  | Bind (T1 : Type) (p1 : proc T1) (p2 : T1 -> proc T).

  (** Semantics: defined using big-step execution relations *)

  Variable State:Type.

  Inductive Result T :=
  | Finished (v:T) (s:State)
  | Crashed (s:State).

  Arguments Crashed {T} s.

  Definition OpSemantics := forall T, Op T -> State -> T -> State -> Prop.

  Context (step : OpSemantics).

  Inductive exec : forall T, proc T -> State -> Result T -> Prop :=
  (* normal execution *)
  | ExecRet : forall T (v:T) s,
      exec (Ret v) s (Finished v s)
  | ExecBindFinished : forall T T' (p: proc T) (p': T -> proc T')
                         s v s' r,
      exec p s (Finished v s') ->
      exec (p' v) s' r ->
      exec (Bind p p') s r
  | ExecOp : forall T (op: Op T) s v s',
      step op s v s' ->
      exec (Prim op) s (Finished v s')

  (* crashing (halting) execution *)
  | ExecCrashBegin : forall T (p: proc T) s,
      exec p s (Crashed s)
  | ExecCrashEnd : forall T (p: proc T) s v s',
      exec p s (Finished v s') ->
      exec p s (Crashed s')
  | ExecBindCrashed : forall T T' (p: proc T) (p': T -> proc T')
                        s s',
      exec p s (Crashed s') ->
      exec (Bind p p') s (Crashed s')
  .

  Definition CrashSemantics := State -> State -> Prop.
  Variable crash_step : CrashSemantics.

  (* [exec_recover] models running recovery with crashes during recovery;
      it's essentially
    (crash_step; exec recovery -> crash)*;  // crashes during recovery
    crash_step; exec recovery -> finished   // eventually recovery runs to completion
   *)
  Inductive exec_recover R (rec:proc R) (s:State) : R -> State -> Prop :=
  | ExecRecoverExec : forall v s' s'',
      crash_step s s' ->
      exec rec s' (Finished v s'') ->
      exec_recover rec s v s''
  | ExecRecoverCrashDuringRecovery : forall s' v s'' s''',
      crash_step s s' ->
      exec rec s' (Crashed s'') ->
      exec_recover rec s'' v s''' ->
      exec_recover rec s v s'''
  .

  Inductive RResult T R :=
  | RFinished (v:T) (s:State)
  | Recovered (v:R) (s:State).

  Arguments RFinished {T R} v s.
  Arguments Recovered {T R} v s.

  (* [rexec] combines the above. A program can execute in one of two ways:
    - exec -> finish (producing RFinished)
    - exec -> crash; exec_recover (producing Recovered)
   *)
  Inductive rexec T R : proc T -> proc R -> State -> RResult T R -> Prop :=
  | RExec : forall (p:proc T) (rec:proc R) s v s',
      exec p s (Finished v s') ->
      rexec p rec s (RFinished v s')
  | RExecCrash : forall (p:proc T) (rec:proc R) s s' rv s'',
      exec p s (Crashed s') ->
      exec_recover rec s' rv s'' ->
      rexec p rec s (Recovered rv s'').

End Proc.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                            (at level 60, right associativity).

Arguments Crashed {State T} s.
Arguments RFinished {State T R} v s.
Arguments Recovered {State T R} v s.
Arguments Ret {Op T} v.
