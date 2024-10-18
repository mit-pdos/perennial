Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.
From New.golang.defn Require Export typing.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Set Default Proof Using "Type".

(** * Typed data representations for struct and slice *)
Module slice.
Record t := mk { ptr_f: loc; len_f: u64; cap_f: u64; }.
Notation nil := slice_nil.
Definition nil_f : slice.t := mk null 0 0.
End slice.

Global Instance into_val_slice `{ffi_syntax} : IntoVal slice.t :=
  {|
    to_val_def (s: slice.t) := InjLV (#s.(slice.ptr_f), #s.(slice.len_f), #s.(slice.cap_f))
  |}.

Global Instance slice_eq_dec : EqDecision slice.t.
Proof. solve_decision. Qed.

Module struct.
Section goose_lang.
  Context `{ffi_syntax}.

  Infix "=?" := (String.eqb).

  Definition val_def (t : go_type) (field_vals: list (string*val)): val :=
    match t with
    | structT d => (fix val_struct (fs : list (string*go_type)) :=
                     match fs with
                     | [] => (#())
                     | (f,ft)::fs => (default (zero_val ft) (assocl_lookup f field_vals), val_struct fs)%V
                     end) d
    | _ => LitV LitPoison
    end.
  Program Definition val := unseal (_:seal (@val_def)). Obligation 1. by eexists. Qed.
  Definition val_unseal : val = _ := seal_eq _.
End goose_lang.
End struct.

Module interface.
Section goose_lang.
  Context `{ffi_syntax}.
  Record t := mk { v: val; mset: list (string * val) }.

  (* FIXME: use the typeid to distinguish nil interface value from nil pointer
     used as a non-nil interface value. *)
  Definition nil_f := mk #null [].
End goose_lang.
End interface.

Global Instance into_val_interface `{ffi_syntax} : IntoVal interface.t :=
  {|
    to_val_def (i: interface.t) :=
      InjLV (#"NO TYPE IDS YET", i.(interface.v), (struct.fields_val i.(interface.mset)))
  |}.

Declare Scope struct_scope.
Notation "f :: t" := (@pair string go_type f%string t) : struct_scope.
Notation "f ::= v" := (@pair string val f%string v%V) (at level 60) : val_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.

(** * Pure Coq reasoning principles *)
Section typing.
  Context `{ffi_sem: ffi_semantics} `{!ffi_interp ffi}.

Program Definition go_type_ind :=
  λ (P : go_type → Prop) (f : P boolT) (f0 : P uint8T) (f1 : P uint16T) (f2 : P uint32T)
  (f3 : P uint64T) (f4 : P int8T) (f5 : P int16T) (f6 : P int32T) (f7 : P int64T)
  (f8 : P stringT) (f9 : ∀ (n : nat) (elem : go_type), P elem → P (arrayT n elem))
  (f10 : ∀ elem : go_type, P elem → P (sliceT elem)) (f11 : P interfaceT)
  (f12 : ∀ (decls : list (string * go_type)) (Hfields : ∀ t, In t decls.*2 → P t), P (structT decls))
  (f13 : P ptrT) (f14 : P funcT) (f15 : ∀ key : go_type, P key → ∀ elem : go_type, P elem → P (mapT key elem))
  (f16 : ∀ elem : go_type, P elem → P (chanT elem)),
  fix F (g : go_type) : P g :=
    match g as g0 return (P g0) with
    | boolT => f
    | uint8T => f0
    | uint16T => f1
    | uint32T => f2
    | uint64T => f3
    | int8T => f4
    | int16T => f5
    | int32T => f6
    | int64T => f7
    | stringT => f8
    | arrayT n elem => f9 n elem (F elem)
    | sliceT elem => f10 elem (F elem)
    | interfaceT => f11
    | structT decls => f12 decls _
    | ptrT => f13
    | funcT => f14
    | mapT key elem => f15 key (F key) elem (F elem)
    | chanT elem => f16 elem (F elem)
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

  | has_go_type_int64 (x : w64) : has_go_type #x int64T
  | has_go_type_int32 (x : w32) : has_go_type #x int32T
  | has_go_type_int16 : has_go_type #null int16T
  | has_go_type_int8 (x : w8) : has_go_type #x int8T

  | has_go_type_string (s : string) : has_go_type #s stringT

  | has_go_type_slice elem (s : slice.t) : has_go_type (#s) (sliceT elem)
  | has_go_type_interface (i : interface.t) : has_go_type (#i) interfaceT

  | has_go_type_array n elem (a : list val)
                      (Hlen : length a = n)
                      (Helems : ∀ v, In v a → has_go_type v elem)
    : has_go_type (fold_right PairV #() a) (arrayT n elem)

  | has_go_type_struct
      (d : struct.descriptor) fvs
      (Hfields : ∀ f t, In (f, t) d → has_go_type (default (zero_val t) (assocl_lookup f fvs)) t)
    : has_go_type (struct.val (structT d) fvs) (structT d)
  | has_go_type_ptr (l : loc) : has_go_type #l ptrT
  | has_go_type_func (f : func.t) : has_go_type #f funcT
  | has_go_type_func_nil : has_go_type #null funcT

  | has_go_type_mapT kt vt (l : loc) : has_go_type #l (mapT kt vt)
  | has_go_type_chanT t (l : loc) : has_go_type #l (chanT t)
  .

  Lemma zero_val_has_go_type t :
    has_go_type (zero_val t) t.
  Proof.
    induction t using go_type_ind; rewrite zero_val_unseal /to_val; try econstructor.
    (* arrayT *)
    { apply length_replicate. }
    { intros. fold zero_val_def in H.
      rewrite -elem_of_list_In in H.
      apply elem_of_replicate_inv in H. subst.
      by rewrite -zero_val_unseal.
    }
    { (* sliceT *)
      replace (zero_val_def (sliceT t)) with (# slice.nil_f).
      { constructor. }
      rewrite to_val_unseal /= //.
    }
    { (* interfaceT *)
      replace (zero_val_def (interfaceT)) with (# interface.nil_f).
      { constructor. }
      rewrite to_val_unseal /= struct.fields_val_unseal /= //.
    }

    { (* structT *)
      replace (zero_val_def (structT decls)) with (struct.val (structT decls) []).
      {
        econstructor. intros. simpl.
        apply Hfields.
        apply in_map_iff. eexists _.
        split; last done. done.
      }
      rewrite struct.val_unseal.
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
      dependent induction a generalizing n.
      + simpl in *. subst. done.
      + simpl. simpl in Hlen.
        destruct n; first by exfalso.
        inversion_clear Hlen. clear n.
        specialize (IHa _ ltac:(done)).
        unshelve epose proof (IHa _ _) as IHa.
        { intros. apply Helems. by right. }
        { intros. apply H. by right. }
        rewrite length_app.
        rewrite IHa Nat.mul_succ_l Nat.add_comm.
        f_equal. apply H. by left.
    - rewrite struct.val_unseal.
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
    | int8T => #(W8 0)
    | int16T => #null
    | int32T => #(W32 0)
    | int64T => #(W64 0)

    | stringT => #("")
    | arrayT n elem => fold_right PairV #() (replicate n (zero_val elem))
    | sliceT _ => #slice.nil_f
    | structT decls => struct.val t []
    | ptrT => #null
    | funcT => #func.nil_f
    | interfaceT => #interface.nil_f
    | mapT _ _ => #null
    | chanT _ => #null
    end.

  Lemma zero_val'_eq_zero_val_1 t :
    zero_val t = zero_val' t.
  Proof.
    rewrite zero_val_unseal.
    induction t; try done.
    { simpl. by rewrite zero_val_unseal. }
    { simpl. rewrite to_val_unseal /= //. }
    { simpl. rewrite to_val_unseal /= struct.fields_val_unseal //. }
    simpl. rewrite struct.val_unseal.
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
  | interfaceT => false (* FIXME: these are currently non-comparable *)
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
  - clear Hlen Helems. simpl in Hcomp.
    induction a.
    + done.
    + rewrite /=. split.
      { apply H0; naive_solver. }
      { apply IHa; naive_solver. }
  - rewrite struct.val_unseal. simpl.
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
  | [ h : (@eq (string * go_type) (_, _) _) |- _ ] =>
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

Program Global Instance into_val_typed_w64_signed : IntoValTyped w64 int64T :=
{| default_val := W64 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.

Program Global Instance into_val_typed_w32_signed : IntoValTyped w32 int32T :=
{| default_val := W32 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.

Program Global Instance into_val_typed_w8_signed : IntoValTyped w8 int8T :=
{| default_val := W8 0 |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.

Program Global Instance into_val_typed_bool : IntoValTyped bool boolT :=
{| default_val := false |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_string : IntoValTyped string stringT :=
{| default_val := "" |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?? [=] //. Qed.

Program Global Instance into_val_typed_slice elemT : IntoValTyped slice.t (sliceT elemT) :=
{| default_val := slice.nil_f |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => ?[???][???] [=] //.
                 repeat intros [=->%to_val_inj]. done.
Qed.

Program Global Instance into_val_typed_func : IntoValTyped func.t funcT :=
{| default_val := func.nil_f |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => [[???] [???]] /= [=] //. naive_solver.
Qed.
Final Obligation. solve_decision. Qed.

Lemma struct_fields_val_inj a b :
  struct.fields_val a = struct.fields_val b →
  a = b.
Proof.
  rewrite struct.fields_val_unseal /= /struct.fields_val_def list.val_unseal.
  dependent induction b generalizing a.
  { by destruct a. }
  destruct a0.
  destruct a as [|[]]; first done.
  rewrite /= => [=].
  intros. subst.
  repeat f_equal.
  - by apply to_val_inj.
  - by apply IHb.
Qed.

Program Global Instance into_val_typed_interface : IntoValTyped interface.t interfaceT :=
{| default_val := interface.nil_f |}.
Next Obligation. solve_has_go_type. Qed.
Next Obligation. rewrite zero_val_eq //. Qed.
Next Obligation. rewrite to_val_unseal => [[??] [??]] /= [??].
                 f_equal; try done.
                 apply struct_fields_val_inj. done.
Qed.
Final Obligation.
  solve_decision.
Qed.

End into_val_instances.
