From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
From iris.bi.lib Require Import fractional.
From Perennial.goose_lang Require Export lang lifting ipersist.
From stdpp Require Import list.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export typing mem.

Section pointsto.
Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Context `{!IntoVal V}.
Implicit Type v : V.
Program Definition typed_pointsto_def l (dq : dfrac) (v : V) : iProp Σ :=
  (([∗ list] j↦vj ∈ flatten_struct (to_val v), heap_pointsto (l +ₗ j) dq vj))%I.
Definition typed_pointsto_aux : seal (@typed_pointsto_def). Proof. by eexists. Qed.
Definition typed_pointsto := typed_pointsto_aux.(unseal).
Definition typed_pointsto_unseal : @typed_pointsto = @typed_pointsto_def := typed_pointsto_aux.(seal_eq).
End pointsto.
Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Section defs.

Class IntoValInj (V : Type) `{IntoVal V} :=
  {
    #[global] to_val_inj :: Inj (=) (=) (to_val (V:=V));
    #[global] to_val_eqdec :: EqDecision V ;
  }.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Class IntoValTyped (V : Type) (t : go.type) `{!IntoVal V} `{!IntoValInj V} :=
  {
    wp_load : (∀ l dq (v : V), {{{ l ↦{dq} v }}}
                                 go.load t #l
                               {{{ RET #v; l ↦{dq} v }}});
    wp_store : (∀ l (v w : V), {{{ l ↦ v }}}
                                 go.store t #l #w
                               {{{ RET #v; l ↦ w }}});
  }.
(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTyped - ! - - : typeclass_instances.
Global Hint Mode IntoValTyped ! - - - : typeclass_instances.
End defs.

Section into_val_instances.
Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.

Program Global Instance into_val_inj_loc : IntoValInj loc.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

(*
Program Global Instance into_val_typed_loc t : IntoValTyped loc (go.PointerType t).
Next Obligation. Admitted.
Next Obligation. Admitted.

Program Global Instance into_val_typed_w64 : IntoValTyped w64 uint64T :=
{| default_val := W64 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w32 : IntoValTyped w32 uint32T :=
{| default_val := W32 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w16 : IntoValTyped w16 uint16T :=
{| default_val := W16 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_w8 : IntoValTyped w8 uint8T :=
{| default_val := W8 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_bool : IntoValTyped bool boolT :=
{| default_val := false |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_string : IntoValTyped go_string stringT :=
{| default_val := ""%go |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_slice : IntoValTyped slice.t sliceT :=
{| default_val := slice.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal. move => [???][???] [=].
                 repeat intros [=->%to_val_inj]. done.
Qed.

(* Using [vec] here because the [to_val] must be a total function that always
   meets [has_go_type]. An alternative could be a sigma type. *)
Program Global Instance into_val_typed_array `{!IntoVal V} `{!IntoValTyped V t} n :
  IntoValTyped (vec V n) (arrayT n t) :=
{| default_val := vreplicate n (default_val _) |}.
Next Obligation.
  rewrite to_val_unseal /=.
  solve_has_go_type.
  induction v as [|].
  - apply (has_go_type_array 0 t []); done.
  - simpl in *.
    inversion IHv. subst.
    pose proof (has_go_type_array (S (length a)) t (#h::a) ltac:(done)) as Ht.
    simpl in Ht. apply Ht. intros ? [|].
    + subst. apply to_val_has_go_type.
    + apply Helems. done.
Qed.
Next Obligation.
  intros.
  rewrite to_val_unseal zero_val_eq /=.
  rewrite -zero_val_unseal -default_val_eq_zero_val.
  induction n; first done. simpl. f_equal. apply IHn.
Qed.
Final Obligation.
rewrite to_val_unseal.
intros. intros ?? Heq.
simpl in Heq.
induction x.
{ rewrite (VectorSpec.nil_spec y) //. }
destruct y using vec_S_inv.
simpl in *.
injection Heq as Heq1 Heq.
apply to_val_inj in Heq1. subst.
f_equal. by apply IHx.
Qed.

Program Global Instance into_val_typed_func : IntoValTyped func.t funcT :=
{| default_val := func.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => [[???] [???]] /= [=] //. naive_solver.
Qed.
Final Obligation. solve_decision. Qed.

Program Global Instance into_val_typed_interface : IntoValTyped interface.t interfaceT :=
{| default_val := interface.nil |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation.
  rewrite to_val_unseal => [x y] Heq.
  destruct x as [|], y as [|].
  {
    simpl in *.
    injection Heq as Heq1 Heq2.
    apply to_val_inj in Heq1. subst. done.
  }
  all: first [discriminate | reflexivity].
Qed.
Final Obligation.
  solve_decision.
Qed.

Program Global Instance into_val_typed_unit : IntoValTyped unit (structT []) :=
{| default_val := tt |}.
Next Obligation.
  intros [].
  replace (#()) with (struct.val_aux (structT []) []).
  2:{ rewrite struct.val_aux_unseal //. }
  by constructor.
Qed.
Next Obligation. rewrite zero_val_eq /= struct.val_aux_unseal //. Qed.
Final Obligation.
  intros ???. destruct x, y. done.
Qed. *)

End into_val_instances.
