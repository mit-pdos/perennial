Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
From New.golang.defn Require Export typing.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

Section alist.

Fixpoint alist_lookup_f {A} (f : go_string) (l : list (go_string * A)) : option A :=
  match l with
  | [] => None
  | (f', v)::l => if ByteString.eqb f' f then Some v else alist_lookup_f f l
  end.

End alist.

(** * Typed data representations for struct and slice *)

Module struct.
Section goose_lang.
  Context `{ffi_syntax}.

  Definition val_aux_def (t : go_type) (field_vals: list (go_string*val)): val :=
    match t with
    | structT d => (fix val_struct (fs : list (go_string*go_type)) :=
                     match fs with
                     | [] => (#())
                     | (f,ft)::fs => (default (zero_val ft) (alist_lookup_f f field_vals), val_struct fs)%V
                     end) d
    | _ => LitV LitPoison
    end.
  Program Definition val_aux := unseal (_:seal (@val_aux_def)). Obligation 1. by eexists. Qed.
  Definition val_aux_unseal : val_aux = _ := seal_eq _.
End goose_lang.
End struct.

Declare Scope struct_scope.
Notation "f :: t" := (@pair go_string go_type f%go t) : struct_scope.
Notation "f ::= v" := (@pair go_string val f%go v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair go_string expr f%go v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.

(** * Pure Coq reasoning principles *)
Section typing.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.

Program Definition go_type_ind :=
  λ (P : go_type → Prop) (f : P boolT) (f0 : P uint8T) (f1 : P uint16T) (f2 : P uint32T)
    (f3 : P uint64T) (f4 : P stringT) (f5 : ∀ (n : nat) (elem : go_type), P elem → P (arrayT n elem))
    (f6 : P sliceT) (f7 : P interfaceT)
    (f8 : ∀ (decls : list (go_string * go_type)) (Hfields : ∀ t, In t decls.*2 → P t), P (structT decls))
    (f9 : P ptrT) (f10 : P funcT),
    fix F (g : go_type) : P g :=
    match g as g0 return (P g0) with
    | boolT => f
    | uint8T => f0
    | uint16T => f1
    | uint32T => f2
    | uint64T => f3
    | stringT => f4
    | arrayT n elem => f5 n elem (F elem)
    | sliceT => f6
    | interfaceT => f7
    | structT decls => f8 decls _
    | ptrT => f9
    | funcT => f10
    end.
Final Obligation.
intros.
revert H.
enough (Forall P decls.*2).
1:{
  intros.
  rewrite List.Forall_forall in H.
  apply H. done.
}
induction decls; first done.
destruct a. apply Forall_cons. split.
{ apply F. }
{ apply IHdecls. }
  Defined.

  Inductive has_go_type : val → go_type → Prop :=
  | has_go_type_bool (b : bool) : has_go_type #b boolT
  | has_go_type_uint64 (x : w64) : has_go_type #x uint64T
  | has_go_type_uint32 (x : w32) : has_go_type #x uint32T
  | has_go_type_uint16 : has_go_type #null uint16T
  | has_go_type_uint8 (x : w8) : has_go_type #x uint8T

  | has_go_type_string (s : go_string) : has_go_type #s stringT

  | has_go_type_slice (s : slice.t) : has_go_type (#s) sliceT
  | has_go_type_interface (i : interface.t) : has_go_type (#i) interfaceT

  | has_go_type_array n elem (a : vec val n)
                      (Helems : ∀ v, In v a → has_go_type v elem)
    : has_go_type (Vector.fold_right PairV a #()) (arrayT n elem)

  | has_go_type_struct
      (d : struct.descriptor) fvs
      (Hfields : ∀ f t, In (f, t) d → has_go_type (default (zero_val t) (alist_lookup_f f fvs)) t)
    : has_go_type (struct.val_aux (structT d) fvs) (structT d)
  | has_go_type_ptr (l : loc) : has_go_type #l ptrT
  | has_go_type_func (f : func.t) : has_go_type #f funcT
  | has_go_type_func_nil : has_go_type #null funcT
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    induction t using go_type_ind; rewrite zero_val_unseal /to_val; try econstructor.
    { intros. fold zero_val_def in H.
      rewrite -elem_of_list_In in H.
      rewrite elem_of_vlookup in H.
      destruct H as [??].
      rewrite vlookup_replicate in H. subst.
      by rewrite -zero_val_unseal.
    }
    { (* structT *)
      replace (zero_val_def (structT decls)) with (struct.val_aux (structT decls) []).
      {
        econstructor. intros. simpl.
        apply Hfields.
        apply in_map_iff. eexists _.
        split; last done. done.
      }
      rewrite struct.val_aux_unseal.
      induction decls.
      { done. }
      destruct a. simpl.
      f_equal.
      { by rewrite zero_val_unseal. }
      apply IHdecls.
      intros.
      apply Hfields.
      simpl. right. done.
    }
  Qed.

  Lemma has_go_type_len {v t} :
    has_go_type v t ->
    length (flatten_struct v) = (go_type_size t).
  Proof.
    rewrite go_type_size_unseal.
    induction 1; simpl; rewrite ?to_val_unseal /=; auto.
    - simpl.
      dependent induction a.
      + simpl in *. subst. done.
      + simpl.
        unshelve epose proof (IHa _ _) as IHa.
        { intros. apply Helems. by right. }
        { intros. apply H. by right. }
        rewrite length_app.
        rewrite IHa.
        f_equal. apply H. by left.
    - rewrite struct.val_aux_unseal.
      induction d.
      { rewrite /= ?to_val_unseal. done. }
      destruct a. cbn.
      rewrite length_app.
      rewrite IHd.
      { f_equal. apply H. by left. }
      { clear H IHd. intros. apply Hfields. by right. }
      { intros. apply H. simpl. by right. }
  Qed.

  Definition zero_val' (t : go_type) : val :=
    match t with
    | boolT => #false

    (* Numeric, except float and impl-specific sized objects *)
    | uint8T => #(W8 0)
    | uint16T => #null
    | uint32T => #(W32 0)
    | uint64T => #(W64 0)

    | stringT => #("")
    | arrayT n elem => Vector.fold_right PairV (vreplicate n (zero_val_def elem)) #()
    | sliceT => #slice.nil
    | structT decls => struct.val_aux t []
    | ptrT => #null
    | funcT => #func.nil
    | interfaceT => #interface.nil
    end.

  Lemma zero_val'_eq_zero_val_1 t :
    zero_val t = zero_val' t.
  Proof.
    rewrite zero_val_unseal.
    induction t; try done.
    simpl. rewrite struct.val_aux_unseal.
    induction decls; first done.
    destruct a. simpl.
    by rewrite IHdecls /= !zero_val_unseal.
  Qed.

  Lemma zero_val_eq :
    zero_val = zero_val'.
  Proof.
    apply functional_extensionality.
    intros. apply zero_val'_eq_zero_val_1.
  Qed.

  #[local] Hint Constructors has_go_type : core.

  Tactic Notation "try_if_one_goal" tactic1(t) :=
    first [ t; let n := numgoals in guard n <= 1
          | idtac ].

  Definition is_slice_val v : {s:slice.t | v = #s} + {∀ (s: slice.t), v ≠ #s}.
  Proof.
    let solve_right :=
      try (solve [ right;
                  intros [???];
                  repeat (rewrite !to_val_unseal /=);
                    inversion 1;
                  subst ]) in
    repeat match goal with
           | l: base_lit |- _ =>
               destruct l; solve_right
           | v: val |- _ =>
               destruct v; solve_right
           end.
    left.
    eexists (slice.mk _ _ _);
      repeat (rewrite !to_val_unseal //=).
  Defined.

  (* TODO: I think this is possible, but some unfortunate changes are needed: we
  need a recursion principle for go_type (which is basically the same as
  go_type_ind but with `In` replaced with something isomorphic to elem_of_list
  but in Type), and then we can finish this up. *)
  Definition has_go_type_dec v t : {has_go_type v t} + {¬has_go_type v t}.
  Proof.
    induction t;
      try_if_one_goal (
          destruct v; eauto; try solve [ right; inversion 1; eauto ];
          try lazymatch goal with
            | l: base_lit |- _ =>
                try_if_one_goal (
                    destruct l; eauto;
                    try solve [ right; inversion 1; eauto ];
                    try lazymatch goal with
                      | l': loc |- _ =>
                          destruct (decide (l' = null)); subst;
                          eauto; try solve [ right; inversion 1; eauto ]
                      end
                  )
          end
        ).
    (* XXX: after changing the "#" notation to refer to IntoVal, this is broken. *)
  Abort.

End typing.

Class IntoValTyped (V : Type) (t : go_type) `{IntoVal V} :=
  {
    default_val : V ;
    to_val_has_go_type: ∀ (v : V), has_go_type (# v) t ;
    default_val_eq_zero_val : #default_val = zero_val t ;
    #[global] to_val_inj :: Inj (=) (=) (to_val (V:=V));
    #[global] to_val_eqdec :: EqDecision V ;
  }.
(* One of [V] or [ty] should not be an evar before doing typeclass search *)
Global Hint Mode IntoValTyped - ! - - : typeclass_instances.
Global Hint Mode IntoValTyped ! - - - : typeclass_instances.
Arguments default_val (V) {_ _ _ _}.

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
    induction a.
    + done.
    + rewrite /=. split.
      { apply H0; naive_solver. }
      { apply IHa; naive_solver. }
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

Program Global Instance into_val_typed_array `{!IntoVal V} `{!IntoValTyped V t} n :
  IntoValTyped (vec V n) (arrayT n t) :=
{| default_val := vreplicate n (default_val _) |}.
Next Obligation.
  rewrite to_val_unseal /=.
  solve_has_go_type.
  induction v as [|].
  - by exfalso.
  - simpl in *. destruct H0.
    + subst. apply to_val_has_go_type.
    + by apply IHv.
Qed.
Next Obligation.
  rewrite to_val_unseal zero_val_eq /= to_val_unseal //.
  intros.
  setoid_rewrite vmap_replicate.
  rewrite -zero_val_unseal.
  rewrite -default_val_eq_zero_val to_val_unseal //.
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
  rewrite to_val_unseal =>[[??] [??]] [Heq ?]. subst.
  do 2 destruct (_ : option (go_string * go_string)).
  {
    f_equal. destruct p, p0. simpl in *.
    injection Heq as Heq1 Heq2.
    apply to_val_inj in Heq1, Heq2.
    intuition. subst. done.
  }
  all: first [discriminate | reflexivity].
Qed.
Final Obligation.
  solve_decision.
Qed.

End into_val_instances.
