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

Module Cond.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  L : interface.t;
}.
End def.
End Cond.

Global Instance settable_Cond `{ffi_syntax}: Settable _ :=
  settable! Cond.mk < Cond.L >.
Global Instance into_val_Cond `{ffi_syntax} : IntoVal Cond.t :=
  {
    to_val_def := λ v, struct.val_aux Cond [("L" ::= #v.(Cond.L))]%V
  }.

Global Program Instance into_val_typed_Cond `{ffi_syntax} : IntoValTyped Cond.t Cond :=
{|
  default_val := Cond.mk (default_val _) ;
  to_val_eqdec := ltac:(solve_decision);
|}.
Next Obligation.
  rewrite to_val_unseal. solve_has_go_type.
Qed.
Next Obligation.
  intros ?. repeat rewrite !to_val_unseal /=. rewrite zero_val_eq.
  repeat rewrite struct.val_aux_unseal /=.
  rewrite zero_val_eq /=.
  repeat rewrite !to_val_unseal /=.
  reflexivity.
Qed.
Final Obligation.
(* FIXME: automation for this *)
rewrite to_val_unseal => ? x y Heq.
rewrite /= struct.val_aux_unseal /= in Heq.
inversion Heq.
destruct x, y.
f_equal.
simpl in *.
apply to_val_inj in H0. subst. done.
Qed.

Program Global Instance into_val_struct_field_Cond_L `{ffi_syntax} : IntoValStructField "L" Cond Cond.L.
Final Obligation.
intros. rewrite to_val_unseal /= struct.val_aux_unseal /= zero_val_eq /= to_val_unseal /=.
rewrite to_val_unseal /=. done.
Qed.

Instance wp_struct_make_Cond `{ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ} L :
  PureWp True
    (struct.make Cond (alist_val [
      "L" ::= #L
    ]))%V
    #(Cond.mk L).
Proof.
  rewrite [in #(_ : Cond.t)]to_val_unseal.
  by apply wp_struct_make.
Qed.
