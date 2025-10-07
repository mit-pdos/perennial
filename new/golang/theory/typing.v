From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Program.Equality.
From iris.bi.lib Require Import fractional.
From Perennial.goose_lang Require Export lang lifting ipersist.
From stdpp Require Import list.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From New.golang.defn Require Export typing mem.

Section defs.

Class IntoValInj (V : Type) `{IntoVal V} :=
  {
    default_val : V ;
    #[global] to_val_inj :: Inj (=) (=) (to_val (V:=V));
    #[global] to_val_eqdec :: EqDecision V ;
  }.
Arguments default_val (V) {_ _ _}.

Context `{sem: ffi_semantics} `{!ffi_interp ffi} `{!heapGS Σ}.
Class IntoValTyped (V : Type) (t : go.type) `{!IntoVal V} `{!IntoValInj V} :=
  {
    typed_pointsto_def (l : loc) (dq : dfrac) (v : V) : iProp Σ;
    wp_load_def : (∀ l dq v, {{{ typed_pointsto_def l dq v }}}
                               go.load t #l
                             {{{ RET #v; typed_pointsto_def l dq v }}}) ;
    wp_store_def : (∀ l v w, {{{ typed_pointsto_def l 1 v }}}
                               go.store t #l #w
                             {{{ RET #v; typed_pointsto_def l 1 w }}}) ;
    wp_alloc_def : ({{{ True }}}
                      go.alloc t #()
                    {{{ l, RET #l; typed_pointsto_def l 1 (default_val V) }}}) ;
  }.
(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTyped - ! - - : typeclass_instances.
Global Hint Mode IntoValTyped ! - - - : typeclass_instances.
Program Definition typed_pointsto := sealed @typed_pointsto_def.
Definition typed_pointsto_unseal : typed_pointsto = _ := seal_eq _.
Arguments typed_pointsto {_ _ _ _ _} l dq v.

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.

Lemma wp_load `{IntoValTyped V t} l dq v :
  {{{ l ↦{dq} v }}}
    go.load t #l
  {{{ RET #v; l ↦{dq} v }}}.
Proof. rewrite typed_pointsto_unseal. apply wp_load_def. Qed.

Lemma wp_store `{IntoValTyped V t} l v w :
  {{{ l ↦ v }}}
    go.store t #l #w
  {{{ RET #v; l ↦ w }}}.
Proof. rewrite typed_pointsto_unseal. apply wp_store_def. Qed.

Lemma wp_alloc `{IntoValTyped V t} :
  {{{ True }}}
    go.alloc t #()
  {{{ l, RET #l; l ↦ (default_val V) }}}.
Proof. rewrite typed_pointsto_unseal. apply wp_alloc_def. Qed.

Fixpoint is_comparable_go_type (t : go_type) : bool :=
  match t with
  | arrayT n elem => is_comparable_go_type elem
  | structT d => forallb (λ '(f, t), is_comparable_go_type t) d
  | funcT => false
  | interfaceT => false
  | _ => true
  end
.

Lemma to_val_is_comparable `{IntoValTyped V t} (v : V) :
  is_comparable_go_type t = true →
  is_comparable #v.
Proof.
  pose proof (to_val_has_go_type v) as Hty.
  generalize dependent #v. clear dependent V.
  intros v Hty Hcomp.
  induction Hty; try rewrite to_val_unseal /= //.
  - repeat constructor; rewrite to_val_unseal //.
  - clear Helems. simpl in Hcomp.
    dependent induction a generalizing n.
    + done.
    + rewrite /=. split.
      { apply H0; naive_solver. }
      { apply (IHa _ ltac:(done)); naive_solver. }
  - rewrite struct.val_aux_unseal. simpl.
    clear Hfields. simpl in Hcomp.
    induction d as [|[]].
    + rewrite /= to_val_unseal //.
    + rewrite /=.
      simpl in Hcomp.
      apply andb_prop in Hcomp as[HcompHd Hcomp].
      split.
      { apply H0; naive_solver. }
      { apply IHd; naive_solver. }
Qed.

Ltac2 solve_has_go_type_step () :=
  match! goal with
  | [ |- has_go_type (zero_val _) _ ] => apply zero_val_has_go_type
  | [ |- has_go_type _ _ ] => try assumption; constructor
  | [ |- Forall _ _ ] => constructor
  | [ |- ∀ (_:_), _ ] => intros
  | [ h : (In _ _) |- _ ] =>
      Std.destruct false [ {
            Std.indcl_arg := (Std.ElimOnIdent h);
            Std.indcl_eqn := None;
            Std.indcl_as := None;
            Std.indcl_in := None
        } ] None
  | [ h : (@eq (go_string * go_type) (_, _) _) |- _ ] =>
      (* XXX: inversion_clear is not as powerful as inversion H; subst; clear H;
      comes up in generics when there are dependent types *)
      Std.inversion Std.FullInversionClear (Std.ElimOnIdent h) None None; cbn
  end.
Ltac solve_has_go_type := repeat ltac2:(solve_has_go_type_step ()).

Section into_val_instances.
Context `{ffi_syntax}.

Program Global Instance into_val_typed_loc : IntoValTyped loc ptrT :=
{| default_val := null |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

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
Qed.

End into_val_instances.

Notation "l ↦ dq v" := (typed_pointsto l dq v%V)
                         (at level 20, dq custom dfrac at level 1,
                            format "l  ↦ dq  v") : bi_scope.
