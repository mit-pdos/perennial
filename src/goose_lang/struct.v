From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import typing.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Set Default Proof Using "Type".
Set Implicit Arguments.

Definition descriptor {ext} {ext_ty: ext_types ext} := list (string*ty).
Definition mkStruct {ext} {ext_ty: ext_types ext} (fs: list (string*ty)): descriptor := fs.

Module one.
  Section goose.
    Context {ext} {ext_ty: ext_types ext}.
    Definition S := mkStruct [("foo", uint64T)].
    Definition v1: val := (#3, #()).
  End goose.
End one.

Module two.
  Section goose.
    Context {ext} {ext_ty: ext_types ext}.
    Definition S := mkStruct [("foo", uint64T); ("bar", boolT)].
    Definition v1: val := (#3, (#true, #())).
  End goose.
End two.

Module three.
  Section goose.
    Context {ext} {ext_ty: ext_types ext}.
    Local Notation "f :: t" := (@pair string ty f%string t%ht).
    Definition S := mkStruct ["foo" :: uint64T; "bar" :: boolT; "baz" :: refT uint64T].
    Definition v1: val := (#3, (#true, (#(LitLoc $ Build_loc 7), #()))).
  End goose.
End three.

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

Example getField1 : getField three.S "foo" = (λ: "v", Fst $ Var "v")%V := eq_refl.
Example getField2 : getField three.S "baz" = (λ: "v", Fst $ Snd $ Snd $ Var "v")%V := eq_refl.
Example getField3 : getField one.S "foo" = (λ: "v", Fst $ Var "v")%V := eq_refl.

Fixpoint getField_f d f0: val -> val :=
  λ v, match d with
       | [] => #()
       | (f,_)::fs =>
         match v with
         | PairV v1 v2 => if f =? f0 then v1 else getField_f fs f0 v2
         | _ => #()
         end
       end.

Example getField_f1 : getField_f three.S "foo" three.v1 = #3 := eq_refl.

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

Example setField_f1 : setField_f three.S "foo" #4 three.v1
                      = (#4, (#true, (#{| loc_car := 7 |}, #())))%V
  := eq_refl.

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

(* Eval vm_compute in build_struct_val
                   three.S
                   [("foo", Val #3);
                   ("baz", Val #{| loc_car := 7 |});
                   ("bar", Val #true)]. *)

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

Definition load_ty t: val :=
  λ: "l",
  (fix load t (l: expr): expr :=
     match t with
     | prodT t1 t2 => (load t1 l, load t2 (l +ₗ[t1] #1))
     | baseT unitBT => #()
     | _ => !l
     end) t (Var "l").

Definition loadStruct (d:descriptor) : val := load_ty (structTy d).

(* Eval cbv -[U64] in structTy three.S. *)
(* Eval cbv -[U64 ty_size Z.mul] in loadStruct three.S. *)

Fixpoint field_offset d f0 : option (Z * ty) :=
  match d with
  | [] => None
  | (f,t)::fs => if f =? f0 then Some (0, t)
               else match field_offset fs f0 with
                    | Some (off, t') => Some (ty_size t + off, t')
                    | None => None
                    end
  end.

(*
Definition fieldPointer (d:descriptor) (f:string) (l:loc): loc :=
  match field_offset d f with
  | Some (off, _) => l +ₗ off
  | None => null
  end.
*)

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

Definition structFieldRef' d f0: val :=
  λ: "p",
  (fix go fs (p: expr): expr :=
     match fs with
     | [] => p
     | (f,t)%core :: fs => if f =? f0 then p
                    else go fs (p +ₗ[t] #1)
     end) d (Var "p").

Definition loadField (d:descriptor) (f:string) : val :=
  match field_offset d f with
  | Some (off, t) => λ: "p", load_ty t (Var "p" +ₗ #off)
  | None => λ: <>, #()
  end.

Definition store_ty t: val :=
  λ: "p" "v",
  (fix store t (p: expr) (v: expr) :=
     match t with
     | prodT t1 t2 => store t1 p (Fst v);;
                     store t2 (p +ₗ[t1] #1) (Snd v)
     | baseT unitBT => #()
     | _ => p <- v
     end) t (Var "p") (Var "v").

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

Theorem load_ty_val_t : forall Γ t,
  Γ ⊢v load_ty t : (structRefT (flatten_ty t) -> t).
Proof using Type.
  intros.
  type_step.
  assert (<[BNamed "l":=structRefT (flatten_ty t)]> Γ ⊢ Var "l" : structRefT (flatten_ty t)) by typecheck.
  generalize dependent (<[BNamed "l":=structRefT (flatten_ty t)]> Γ).
  generalize dependent (Var "l").
  induction t; simpl; intros; eauto;
     try solve [ typecheck ].
  { destruct t; simpl; typecheck. }
  type_step.
  - eapply IHt1.
    eapply struct_weaken_hasTy; eauto.
  - eapply IHt2.
    admit. (* TODO: need to fix typing rules to use scaled offset *)
Admitted.

Theorem load_ty_t : forall Γ t,
  Γ ⊢ load_ty t : (structRefT (flatten_ty t) -> t).
Proof.
  constructor.
  apply load_ty_val_t.
Qed.

Theorem loadStruct_t Γ d :
  Γ ⊢v loadStruct d : (structRefTy d -> structTy d).
Proof.
  unfold loadStruct.
  apply load_ty_val_t.
Qed.

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

Theorem loadField_t : forall d f t z,
  field_offset d f = Some (z, t) ->
  forall Γ, (Γ ⊢v loadField d f : (structRefTy d -> t))%T.
Proof.
  unfold structRefTy, loadField; simpl.
  intros.
  rewrite H; simpl.
  type_step.
  econstructor; [ | apply load_ty_t ].
  eapply fieldOffset_t; eauto.
  typecheck.
Qed.

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

Theorem store_ty_val_t : forall Γ t,
  Γ ⊢v store_ty t : (structRefT (flatten_ty t) -> t -> unitT).
Proof using Type.
  (* TODO: copy the structure of load_ty *)
Admitted.

Theorem store_ty_t Γ t :
  Γ ⊢ store_ty t : (structRefT (flatten_ty t) -> t -> unitT).
Proof.
  constructor.
  apply store_ty_val_t.
Qed.

Theorem storeStruct_t : forall Γ d,
  Γ ⊢v storeStruct d : (structRefTy d -> structTy d -> unitT).
Proof.
  unfold storeStruct; intros.
  apply store_ty_val_t.
Qed.

Theorem storeField_t : forall Γ d f z t,
  field_offset d f = Some (z, t) ->
  Γ ⊢v storeField d f : (structRefTy d -> t -> unitT).
Proof.
  unfold storeField; intros.
  rewrite H.
  type_step.
  type_step.
  eapply app_hasTy; [ typecheck | ].
  eapply app_hasTy.
  { (* eapply fieldOffset_t; eauto. *) admit. }
  apply store_ty_t; eauto.
Admitted.

End goose_lang.

Declare Reduction getField := cbv [getField rev fst snd app String.eqb Ascii.eqb eqb].

Ltac make_structF desc fname :=
  let f := eval unfold desc in (getField desc fname) in
  let f := eval getField in f in
      lazymatch f with
      | context[LitUnit] => fail "struct" desc "does not have field" fname
      | _ => exact f
      end.

(* we don't use this, but just to document the relevant reduction *)
Declare Reduction buildStruct :=
  cbv [buildStruct
       build_struct_val
       rev app assocl_lookup
       String.eqb Ascii.eqb eqb].

Module struct.
  Notation decl := mkStruct.
  Notation mk := buildStruct.
  Notation new := allocStructLit.
  Notation alloc := allocStruct.
  Notation get := getField.
  Notation fieldRef := structFieldRef.
  (* TODO: load/loadF could probably use better names *)
  Notation load := loadStruct.
  Notation loadF := loadField.
  Notation t := structTy.
  Notation ptrT := structRefTy.
  Notation store := storeStruct.
  Notation storeF := storeField.
End struct.

Notation "![ t ] e" := (load_ty t e%E)
                         (at level 9, right associativity, format "![ t ]  e") : expr_scope.
Notation "e1 <-[ t ] e2" := (store_ty t e1%E e2%E)
                             (at level 80, format "e1  <-[ t ]  e2") : expr_scope.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing).

Notation "f :: t" := (@pair string ty f%string t%ht).
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.

(* TODO: we'll again need to unfold these to prove theorems about them, but
for typechecking they should be opaque *)
Global Opaque allocStruct structFieldRef loadStruct loadField storeStruct storeField.
Hint Resolve structFieldRef_t loadStruct_t loadField_t storeStruct_t storeField_t : types.
