From New.golang Require Import theory.
From New.code Require Export sync.

Module Mutex.
Record t := mk {
    state : bool
}.
End Mutex.

Global Instance into_val_Mutex `{ffi_syntax} : IntoVal Mutex.t :=
  {|
    to_val_def := λ v, struct.val_aux Mutex [("state" ::= #v.(Mutex.state))]%V
  |}.

Global Program Instance into_val_typed_Mutex `{ffi_syntax} : IntoValTyped Mutex.t Mutex :=
{| default_val := Mutex.mk false |}.
Next Obligation. rewrite to_val_unseal /=. solve_has_go_type. Qed.
Next Obligation.
  (* FIXME: [solve_zero_val] tactic *)
  intros. rewrite zero_val_eq to_val_unseal /= struct.val_aux_unseal /=.
  rewrite zero_val_eq /= !to_val_unseal //.
Qed.
Next Obligation.
  (* FIXME: automation for this *)
  rewrite to_val_unseal => ? x y Heq.
  rewrite /= struct.val_aux_unseal /= in Heq.
  inversion Heq.
  destruct x, y.
  f_equal.
  simpl in *.
  apply to_val_inj in H0. subst. done.
Qed.
Final Obligation. solve_decision. Qed.

Global Program Instance into_val_struct_Mutex_state `{ffi_syntax} :
  IntoValStructField "state" Mutex Mutex.state.
Final Obligation.
intros. by rewrite to_val_unseal /= struct.val_aux_unseal /= to_val_unseal /=.
Qed.
