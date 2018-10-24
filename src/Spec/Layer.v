Require Import Spec.Proc.
Require Import Spec.Abstraction.
Require Import Helpers.RelationAlgebra.

Import RelationNotations.

Record Layer Op :=
  { State: Type;
    sem: Dynamics Op State;
    (* TODO: add init here *) }.

(* LayerImpl is just the code needed to translate from one layer to another -
   the logical components are in [LayerRefinement] *)
Record LayerImpl C_Op Op :=
  { compile_op `(op: Op T) : proc C_Op T;
    (* TODO: layer implementations should be allowed returning from recovery
         (though it's unclear what purpose that would serve *)
    recover: proc C_Op unit;
  (* TODO: add init here *) }.

Section Layers.

  Context C_Op (c_layer: Layer C_Op).
  Notation CState := c_layer.(State).
  Notation c_sem := c_layer.(sem).
  Notation c_proc := (proc C_Op).

  Context Op (a_layer: Layer Op).
  Notation AState := a_layer.(State).
  Notation a_sem := a_layer.(sem).
  Notation a_proc := (proc Op).

  Context (impl: LayerImpl C_Op Op).
  Notation compile_op := impl.(compile_op).
  Notation recover := impl.(recover).

  Definition compile_op_refines_step (abs: AState -> CState -> Prop) :=
    forall T (op: Op T),
      crash_refines abs c_sem
                    (compile_op op) recover
                    (a_sem.(step) op)
                    (* same as [(pure tt + (a_sem.(step) op;; pure tt));;
                       a_sem.(crash_step)], but easier to write due to
                       parsing *)
                    (a_sem.(crash_step) +
                     (a_sem.(step) op;; a_sem.(crash_step))).

  Definition recovery_refines_noop (abs: AState -> CState -> Prop) :=
    crash_refines abs c_sem
                  recover
                  recover
                  any (* normal behavior of recovery is irrelevant, we never ask
                  how it runs normally *)
                  (a_sem.(crash_step)).

  Record LayerRefinement :=
    { abs: AState -> CState -> Prop;
      compile_op_ok : compile_op_refines_step abs;
      recovery_ok : recovery_refines_noop abs;
      (* TODO: init_ok *) }.

  Fixpoint compile T (p: a_proc T) : c_proc T :=
    match p with
    | Prim op => compile_op op
    | Ret v => Ret v
    | Bind p p' => Bind (compile p) (fun v => compile (p' v))
    end.

End Layers.
