Require Export New.code.sync.
From New.proof Require Import proof_prelude.

(* Begin manually written version of proofgen output *)
Module Mutex.
Record t := mk {
    state : bool
}.
End Mutex.

Section instances.
Context `{ffi_syntax}.
Global Instance into_val_Mutex : IntoVal Mutex.t :=
  {|
    to_val_def := λ v, struct.val_aux sync.Mutex [("state" ::= #v.(Mutex.state))]%struct
  |}.

Global Program Instance into_val_typed_Mutex : IntoValTyped Mutex.t sync.Mutex :=
{| default_val := Mutex.mk (default_val _) |}.
Next Obligation. rewrite to_val_unseal /=; solve_has_go_type. Qed.
Next Obligation. solve_zero_val. Qed.
Next Obligation. solve_to_val_inj. Qed.
Final Obligation. solve_decision. Qed.

Global Instance into_val_struct_Mutex_state :
  IntoValStructField "state" sync.Mutex Mutex.state.
Proof. solve_into_val_struct_field. Qed.

Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.

Global Instance wp_struct_make_Mutex (state : bool) :
  PureWp True
    (struct.make #sync.Mutex (alist_val [
      "state" ::= #state
    ]))%struct
    #(Mutex.mk state).
Proof. solve_struct_make_pure_wp. Qed.

Global Instance Mutex_struct_split dq l (v : Mutex.t) :
  StructFieldsSplit dq l v (
      "Hstate" ∷ l ↦s[sync.Mutex :: "state"]{dq} v.(Mutex.state)
    ).
Proof.
  rewrite /named.
  apply struct_fields_split_intro.
  unfold_typed_pointsto; split_pointsto_app.

  rewrite -!/(typed_pointsto_def _ _ _) -!typed_pointsto_unseal.
  solve_field_ref_f.
Qed.
End instances.

Module Cond.
Section def.
Context `{ffi_syntax}.
Record t := mk {
  L : interface.t;
}.
End def.
End Cond.

Section instances.
Context `{ffi_syntax}.

Global Instance settable_Cond : Settable _ :=
  settable! Cond.mk < Cond.L >.
Global Instance into_val_Cond : IntoVal Cond.t :=
  {
    to_val_def := λ v, struct.val_aux sync.Cond [("L" ::= #v.(Cond.L))]%struct
  }.

Global Program Instance into_val_typed_Cond : IntoValTyped Cond.t sync.Cond :=
{|
  default_val := Cond.mk (default_val _) ;
  to_val_eqdec := ltac:(solve_decision);
|}.
Next Obligation.
  rewrite to_val_unseal. solve_has_go_type.
Qed.
Next Obligation.
  repeat rewrite !to_val_unseal /=. rewrite zero_val_eq.
  repeat rewrite struct.val_aux_unseal /=.
  rewrite zero_val_eq /=.
  repeat rewrite !to_val_unseal /=.
  reflexivity.
Qed.
Final Obligation.
(* FIXME: automation for this *)
rewrite to_val_unseal => x y Heq.
rewrite /= struct.val_aux_unseal /= in Heq.
inversion Heq.
destruct x, y.
f_equal.
simpl in *.
apply to_val_inj in H1. subst. done.
Qed.

Program Global Instance into_val_struct_field_Cond_L : IntoValStructField "L" sync.Cond Cond.L.
Final Obligation.
intros. rewrite to_val_unseal /= struct.val_aux_unseal /= zero_val_eq /= to_val_unseal /=.
rewrite to_val_unseal /=. done.
Qed.

Context `{!ffi_model, !ffi_semantics _ _, !ffi_interp _, !heapGS Σ}.

Global Instance wp_struct_make_Cond L :
  PureWp True
    (struct.make #sync.Cond (alist_val [
      "L" ::= #L
    ]))%struct
    #(Cond.mk L).
Proof.
  rewrite [in #(_ : Cond.t)]to_val_unseal.
  by apply wp_struct_make.
Qed.

Global Instance Cond_struct_split dq l (v : Cond.t) :
  StructFieldsSplit dq l v (
      "HL" ∷ l ↦s[sync.Cond :: "L"]{dq} v.(Cond.L)
    ).
Admitted.

End instances.
(* End manually written version of recordgen output *)
