Require Import Spec.Proc.
Require Import Spec.ProcTheorems.
Require Import Helpers.RelationAlgebra.
Require Import Helpers.RelationRewriting.
Require Import Helpers.RelationTheorems.
Require Import Tactical.ProofAutomation.

Import RelationNotations.
Require FunctionalExtensionality.

Record Layer Op :=
  { OpState: Type;
    sem: Dynamics Op OpState;
    (* TODO: should these be part of Dynamics instead of Layer? *)
    trace_proj: OpState -> list Event;
    crash_preserves_trace:
      forall s1 s2, sem.(crash_step) s1 (Val s2 tt) -> trace_proj s1 = trace_proj s2;
    crash_total: forall s1, exists s2, sem.(crash_step) s1 (Val s2 tt);
    crash_non_err: forall s1 ret, sem.(crash_step) s1 ret -> ret <> Err;
    initP: OpState -> Prop }.

Inductive InitStatus := Initialized | InitFailed.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed to return from recovery
         (though it's unclear what purpose that would serve *)
    recover: rec_seq C_Op;
    (* init: proc C_Op InitStatus; *) }.

Definition State `(L: Layer Op) := @Proc.State (L.(OpState)).

Fixpoint compile Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  match p with
  | Call op => impl.(compile_op) op
  | Ret v => Ret v
  | Bind p p' => Bind (impl.(compile) p) (fun v => impl.(compile) (p' v))
  | Loop b init => Loop (fun mt => impl.(compile) (b mt)) init
  | Unregister => Unregister
  | Wait => Wait
  | Spawn p => Spawn (impl.(compile) p)
  end.

(* TODO: add call to 'close' after the wait *)
Import ProcNotations.
Definition compile_whole Op C_Op `(impl: LayerImpl C_Op Op) T (p: proc Op T) : proc C_Op T :=
  Bind (impl.(compile) p) (fun v => _ <- Wait; Ret v)%proc.

Fixpoint map_proc_seq {Op C_Op T} (f: forall T, proc Op T -> proc C_Op T) (es: proc_seq Op T) :=
  match es with
  | Proc_Seq_Final e => Proc_Seq_Final (f _ e)
  | @Proc_Seq_Bind _ _ _  e es' =>
    Proc_Seq_Bind (f _ e) (fun x => map_proc_seq f (es' x))
  end.

Fixpoint compile_seq Op C_Op `(impl: LayerImpl C_Op Op) (ps: rec_seq Op) :
  rec_seq C_Op :=
  match ps with
  | Seq_Nil => Seq_Nil
  | Seq_Cons p ps' => Seq_Cons (impl.(compile_whole) p) (impl.(compile_seq) ps')
  end.

Definition compile_proc_seq Op C_Op T `(impl: LayerImpl C_Op Op) (ps: proc_seq Op T) :=
  map_proc_seq (impl.(compile_whole)) ps.

Definition compile_rec Op C_Op `(impl: LayerImpl C_Op Op) (rec: rec_seq Op) : rec_seq C_Op :=
  rec_seq_append impl.(recover) (impl.(compile_seq) rec).

Coercion sem : Layer >-> Dynamics.
