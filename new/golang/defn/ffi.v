From New Require Export notation.
From New.golang.theory Require Import typing.
From Perennial Require Import base.
From Perennial.Helpers Require Import Transitions.
From RecordUpdate Require Import RecordSet.

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

Local Existing Instance fallback_genPred.
Existing Instances r_mbind r_mret r_fmap.

Definition cast {T} {A A' : T} {P : T → Type} (eq_pf : A = A') (a : P A) : P A' :=
  match eq_pf in (_ = t) return P t with
  | eq_refl => a
  end.

Definition models_ffi_step (op : (go_string * go_string)) (v : val) :=
  let '(model_name, op_name) := op in
  let m := M model_name in
  '(e, w, gw) ← (suchThat (λ '(σ, g) '(e, w, gw),
                    relation.denote (m.(model.step) op_name v)
                      ((σ.(world) : models_state) model_name, (g.(global_world) : models_global_state) model_name)
                      (w, gw) e));
  modify (λ '(σ, g), (set world
                        (λ _, λ n,
                           match decide (model_name = n) with
                           | right _ => σ.(world) n
                           | left eq_pf => cast eq_pf w
                           end) σ,
                        set global_world
                          (λ _, λ n,
                             match decide (model_name = n) with
                             | right _ => g.(global_world) n
                             | left eq_pf => cast eq_pf gw
                             end) g));;
  ret (#() #()) : transition (state * global_state) expr.

Definition models_ffi_crash_step (s s' : models_state) :=
  ∀ name, (M name).(model.crash_step) (s name) (s' name).

Instance models_ffi_semantics : ffi_semantics models_syntax _ :=
  {|
    ffi_step := models_ffi_step;
    ffi_crash_step := models_ffi_crash_step;
  |}.

End to_ffi.

(* TODO: belongs in untrusted theory. *)
(*
Class model_interp (model : model.t) :=
  {
    modelLocalGS: gFunctors -> Set;
    modelGlobalGS: gFunctors -> Set;
    model_global_ctx: ∀ `{modelGlobalGS Σ}, model_global_state -> iProp Σ;
    model_local_ctx: ∀ `{modelLocalGS Σ}, model_state -> iProp Σ;
    model_global_start: ∀ `{modelGlobalGS Σ}, model_global_state -> iProp Σ;
    model_local_start: ∀ `{modelLocalGS Σ}, model_state -> iProp Σ;
    (* model_restart is provided to the client in idempotence_wpr *)
    model_restart: ∀ `{modelLocalGS Σ}, model_state -> iProp Σ;
    model_crash_rel: ∀ Σ, modelLocalGS Σ → model_state → modelLocalGS Σ → model_state → iProp Σ;
  }.
 *)
