From stdpp Require Import gmap.
From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import typing.

(** * Struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Set Default Proof Using "Type".
Set Implicit Arguments.

Section goose.
  Context {ext} {ext_ty: ext_types ext}.
  Definition descriptor := list (string*ty).
  Definition mkStruct (fs: list (string*ty)): descriptor := fs.

  Class descriptor_wf (d:descriptor) :=
    { descriptor_NoDup: NoDup d.*1; }.

  Definition option_descriptor_wf (d:descriptor) : option (descriptor_wf d).
    destruct (decide (NoDup d.*1)); [ apply Some | apply None ].
    constructor; auto.
  Defined.
End goose.

Local Ltac maybe_descriptor_wf d :=
  let mpf := (eval hnf in (option_descriptor_wf d)) in
  match mpf with
  | Some ?pf => exact pf
  | None => fail "descriptor is not well-formed"
  end.

Hint Extern 3 (descriptor_wf ?d) => maybe_descriptor_wf d : typeclass_instances.

Section goose_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty: ext_types ext}.

Implicit Types (d:descriptor).

Infix "=?" := (String.eqb).

Definition getField d (f0: string) : val :=
  λ: "v",
  (fix go fs e : expr :=
     match fs with
     | [] => #()
     | (f,_)%core::fs => if f =? f0 then Fst e else go fs (Snd e)
     end) d (Var "v").

Fixpoint getField_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else getField_f fs f0 v2
         | _ => #()
         end
       end.

Fixpoint setField_f d f0 fv: val -> val :=
  λ v, match d with
       | [] => v
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 =>
           if f =? f0
           then PairV fv v2
           else PairV v1 (setField_f fs f0 fv v2)
         | _ => v
         end
       end.

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if f =? f0 then Some v else assocl_lookup fs f0
  end.

Fixpoint build_struct_val d (field_vals: list (string*expr)): option expr :=
  let lookup_f := assocl_lookup field_vals in
  match d with
  | [] => Some (Val #())
  | (f,_)::fs => match lookup_f f with
           | Some e => match build_struct_val fs field_vals with
                      | Some e' => Some (e, e')%E
                      | None => None
                      end
           | None => None
           end
  end.

Definition buildStruct d (fvs: list (string*expr)) : expr :=
  match build_struct_val d fvs with
  | Some v => v
  | None => LitV LitUnit
  end.

(* wraps AllocStruct for typechecking *)
Definition allocStruct (d:descriptor) : val :=
  λ: "v", Alloc (Var "v").

Definition allocStructLit (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val d fvs with
  | Some v => Alloc v
  | None => LitV LitUnit
  end.

Fixpoint structTy d : ty :=
  match d with
  | [] => unitT
  | (_,t)::fs => prodT t (structTy fs)
  end.

Definition structRefTy (d:descriptor) : ty :=
  structRefT (flatten_ty (structTy d)).

Fixpoint load_ty t: val :=
  match t with
  | prodT t1 t2 => λ: "l", (load_ty t1 (Var "l"), load_ty t2 (Var "l" +ₗ[t1] #1))
  | baseT unitBT => λ: <>, #()
  | _ => λ: "l", !(Var "l")
  end.

Definition loadStruct (d:descriptor) : val := load_ty (structTy d).

Fixpoint field_offset d f0 : option (Z * ty) :=
  match d with
  | [] => None
  | (f,t)::fs => if f =? f0 then Some (0, t)
               else match field_offset fs f0 with
                    | Some (off, t') => Some (ty_size t + off, t')
                    | None => None
                    end
  end.

Definition fieldType (d:descriptor) (f:string): ty :=
  match field_offset d f with
  | Some (_, t) => t
  | None => unitT
  end.

(** structFieldRef gives a function that takes a location and constant pointer
arithmetic on it (which is pre-computed based on the field and descriptor). *)
Definition structFieldRef d f0: val :=
  match field_offset d f0 with
  | Some (off, t) => λ: "p", BinOp (OffsetOp off) (Var "p") #1
  | None => λ: <>, #()
  end.

Definition loadField (d:descriptor) (f:string) : val :=
  match field_offset d f with
  | Some (off, t) => λ: "p", load_ty t (BinOp (OffsetOp off) (Var "p") #1)
  | None => λ: <>, #()
  end.

Fixpoint store_ty t: val :=
  match t with
  | prodT t1 t2 => λ: "p" "v",
                  store_ty t1 (Var "p") (Fst (Var "v"));;
                  store_ty t2 (Var "p" +ₗ[t1] #1) (Snd (Var "v"))
  | baseT unitBT => λ: <> <>, #()
  | _ => λ: "p" "v", Var "p" <- Var "v"
  end.

Definition storeStruct (d: descriptor) : val := store_ty (structTy d).

Definition storeField d f : val :=
  match field_offset d f with
  | Some (off, t) => λ: "p" "x", store_ty t (BinOp (OffsetOp off) (Var "p") #1) (Var "x")
  | None => λ: <> <>, #()
  end.

Hint Resolve struct_offset_op_hasTy_eq : types.

Local Open Scope heap_types.

Theorem load_struct_ref_hasTy Γ l t ts :
  Γ ⊢ l : structRefT (t::ts) ->
  Γ ⊢ !l : t.
Proof.
  intros.
  apply load_hasTy.
  eapply struct_weaken_hasTy; simpl; eauto.
Qed.

Theorem load_structRef_off : forall Γ e ts n t,
  ts !! Z.to_nat n = Some t ->
  (Γ ⊢ e : structRefT ts)%T ->
  (Γ ⊢ ! (e +ₗ #n) : t)%T.
Proof.
  intros.
  destruct (elem_of_list_split_length ts (Z.to_nat n) t)
    as [l1 [l2 (?&?)]]; auto; subst.
  eapply load_struct_ref_hasTy.
  eapply struct_offset_op_hasTy_eq; eauto.
  rewrite drop_app_alt; auto.
Qed.

Hint Resolve load_structRef_off : types.

Hint Rewrite ty_size_length : ty.

Theorem struct_offset_0_hasTy Γ ts e :
  Γ ⊢ e : structRefT ts ->
  Γ ⊢ (e +ₗ #0) : structRefT ts.
Proof.
  apply struct_offset_op_hasTy.
Qed.

Hint Resolve load_hasTy.

Hint Rewrite @drop_app : ty.

Theorem fieldOffset_t Γ fs f z t e :
  field_offset fs f = Some (z, t) ->
  Γ ⊢ e : structRefT (flatten_ty (structTy fs)) ->
  Γ ⊢ (e +ₗ #z) : structRefT (flatten_ty t).
Proof using Type.
  revert e z t.
  induction fs; simpl; intros.
  - congruence.
  - destruct a as [f' t']; simpl in H0.
    destruct (f' =? f)%string.
    + inversion H; subst; clear H.
      apply struct_offset_0_hasTy.
      eapply struct_weaken_hasTy; eauto.
    + destruct_with_eqn (field_offset fs f); try congruence.
      destruct p as [off t''].
      inversion H; subst; clear H.

      apply struct_offset_op_collapse_hasTy; auto.
      eapply IHfs; eauto.

      eapply struct_offset_op_hasTy_eq; eauto.
      autorewrite with ty.
      destruct fs; simpl in *; congruence.
Qed.

(*
Theorem loadField_t : forall d f t z,
  field_offset d f = Some (z, t) ->
  forall Γ, (Γ ⊢v loadField d f : (structRefTy d -> t))%T.
Proof.
  unfold structRefTy, loadField; simpl.
  intros.
  rewrite H; simpl.
  type_step.
  econstructor; [ | apply load_ty'_t ].
  eapply fieldOffset_t; eauto.
  typecheck.
  rewrite lookup_insert //=.
Qed.
*)

Theorem structFieldRef_t Γ d f t z :
  field_offset d f = Some (z, t) ->
  Γ ⊢v structFieldRef d f : (structRefTy d -> structRefT (flatten_ty t)).
Proof.
  unfold structRefTy, structFieldRef.
  intros.
  rewrite H.
  type_step.
  admit. (* more scaled offset typing *)
Admitted.

Hint Constructors expr_hasTy.

Theorem store_struct_singleton Γ e v t :
  Γ ⊢ e : structRefT [t] ->
  Γ ⊢ v : t ->
  Γ ⊢ (e <- v) : unitT.
Proof.
  intros.
  eapply store_hasTy; eauto.
Qed.

Hint Resolve store_struct_singleton.

End goose_lang.

Module struct.
  Notation decl := mkStruct.
  Notation wf := descriptor_wf.

  Notation t := structTy.
  Notation ptrT := structRefTy.

  Notation mk := buildStruct.
  Notation new := allocStructLit.
  Notation alloc := allocStruct.
  Notation get := getField.
  Notation fieldRef := structFieldRef.
  Notation load := loadStruct.
  Notation loadF := loadField.
  Notation store := storeStruct.
  Notation storeF := storeField.
End struct.

Notation "![ t ] e" := (load_ty t e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (store_ty t e1%E e2%E)
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.

Notation "f :: t" := (@pair string ty f%string t%ht) : struct_scope.
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
Delimit Scope struct_scope with struct.
Arguments mkStruct {ext ext_ty} _%struct_scope.
Open Scope struct_scope.

(* TODO: we'll again need to unfold these to prove theorems about them, but
for typechecking they should be opaque *)
Global Opaque allocStruct structFieldRef loadStruct loadField storeStruct storeField.
