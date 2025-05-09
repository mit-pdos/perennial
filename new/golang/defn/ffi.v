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

Definition invalid_model :=
  model.mk unit unit (λ _ _, undefined) (λ _ _, True).

Definition models : Type := go_string → model.t .

Section to_ffi.
Context {M : models}.

Definition models_state := ∀ name, (M name).(model.state).

Definition models_global_state := ∀ name, (M name).(model.global_state).

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
    let m := M model_name in
    undefined
      (* TODO: lift to [models] *)
      (* m.(model.step) op_name v *)
    : transition (state * global_state) expr.

Definition models_ffi_crash_step (s s' : models_state) :=
  ∀ name, (M name).(model.crash_step) (s name) (s' name).

Instance models_ffi_semantics : ffi_semantics models_syntax _ :=
  {|
    ffi_step := models_ffi_step;
    ffi_crash_step := models_ffi_crash_step;
  |}.

End to_ffi.
