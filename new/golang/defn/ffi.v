From New Require Export notation.
From New.golang.theory Require Import typing.
From Perennial Require Import base.
From Perennial.Helpers Require Import Transitions.

Local Instance models_syntax : ffi_syntax :=
  {|
    ffi_opcode := (go_string * go_string);
    ffi_val := Empty_set;
  |}.

Module model.
  Record t :=
    mk {
        global_state : Type;
        state : Type;
        step : go_string -> val -> transition (state*global_state) expr;
        crash_step : state -> state -> Prop;
        #[global] state_inhabited :: Inhabited state;
        #[global] global_state_inhabited :: Inhabited global_state;
      }.
End model.

Class models : Type :=
  {
    model_names : gset go_string;
    models_lookup : { model_name : go_string & (model_name ∈ model_names) } → model.t;
  }.

Section to_ffi.
Context {M : models}.

Local Notation model_names_type := { model_name : go_string & (model_name ∈ model_names) }.

Definition models_state : Type :=
  ∀ (name : model_names_type), (models_lookup name).(model.state).

Definition models_global_state : Type :=
  ∀ (name : model_names_type), (models_lookup name).(model.global_state).

Program Instance models_ffi_model : ffi_model :=
  {|
    ffi_state := models_state;
    ffi_global_state := models_global_state;
  |}.
Next Obligation.
  refine (populate (fun _ => inhabitant)).
Qed.
Final Obligation.
  refine (populate (fun _ => inhabitant)).
Qed.

Definition models_ffi_step :=
  λ (op : ffi_opcode) (v : val),
    let '(model_name, op_name) := op in
    match decide (model_name ∈ model_names) with
    | right _ =>  undefined
    | left in_pf =>
        let m := models_lookup (existT model_name in_pf) in
        undefined
        (* TODO: lift to [models] *)
        (* m.(model.step) op_name v *)
    end : transition (state * global_state) expr.

Definition models_ffi_crash_step (s s' : models_state) :=
  ∀ (m : model_names_type), (models_lookup m).(model.crash_step) (s m) (s' m).

Instance models_ffi_semantics : ffi_semantics models_syntax _ :=
  {|
    ffi_step := models_ffi_step;
    ffi_crash_step := models_ffi_crash_step;
  |}.

End to_ffi.
