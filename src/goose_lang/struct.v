From Perennial.goose_lang Require Export lang.
From Perennial.goose_lang Require Import notation.
From Perennial.goose_lang Require Import typing.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Set Default Proof Using "Type".

Section goose_lang.
  Context `{ffi_sem: ext_semantics}.
  Context {ext_ty: ext_types ext}.

Record descriptor :=
  mkStruct { fields: list (string*ty); }.

Fixpoint getField_e (f0: string) (rev_fields: list (string*ty)) (se: expr): expr :=
  match rev_fields with
  | [] => LitV LitUnit
  | [(f,_)] => if String.eqb f f0 then se else #()
  | (f,_)::fs => if String.eqb f f0 then Snd se else getField_e f0 fs (Fst se)
  end.

Definition getField (d:descriptor) f : val :=
  λ: "v", getField_e f (rev d.(fields)) (Var "v").

Definition val_fst (p : val) : val :=
  match p with
  | PairV a b => a
  | _ => #()
  end.

Definition val_snd (p : val) : val :=
  match p with
  | PairV a b => b
  | _ => #()
  end.

Fixpoint extractField_helper (f0: string) (rev_fields: list (string*ty)) (v: val): val :=
  match rev_fields with
  | [] => #()
  | [f] => if String.eqb (fst f) f0 then v else #()
  | f::fs => if String.eqb (fst f) f0 then val_snd v else extractField_helper f0 fs (val_fst v)
  end.

Definition extractField (d:descriptor) f v : val :=
  extractField_helper f (rev d.(fields)) v.

Fixpoint updateField_helper (rev_fields: list (string*ty)) (f0: string) (f0v: val) (oldv: val): val :=
  match rev_fields with
  | [] => #()
  | [f] => if String.eqb (fst f) f0 then f0v else oldv
  | f::fs =>
    PairV (updateField_helper fs f0 f0v (val_fst oldv))
          (if String.eqb (fst f) f0 then f0v else val_snd oldv)
  end.

Definition updateField (d:descriptor) f fv v : val :=
  updateField_helper (rev d.(fields)) f fv v.

Fixpoint assocl_lookup {A} (field_vals: list (string * A)) (f0: string) : option A :=
  match field_vals with
  | [] => None
  | (f, v)::fs => if String.eqb f f0 then Some v else assocl_lookup fs f0
  end.

Fixpoint build_struct_val
         (field_vals: list (string * expr))
         (rev_fields: list (string * ty)) : option expr :=
  match rev_fields with
  | [] => None
  | [f] => assocl_lookup field_vals (fst f)
  | f::fs => match assocl_lookup field_vals (fst f) with
           | Some v => match build_struct_val field_vals fs with
                      | Some vs => Some (vs, v)%E
                      | None => None
                      end
           | None => None
           end
  end.

Definition buildStruct (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val fvs (rev d.(fields)) with
  | Some v => v
  | None => LitV LitUnit
  end.

(* wraps AllocStruct for typechecking *)
Definition allocStruct (d:descriptor) : val :=
  λ: "v", Alloc (Var "v").

Definition allocStructLit (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val fvs (rev d.(fields)) with
  | Some v => Alloc v
  | None => LitV LitUnit
  end.

Fixpoint struct_ty_aux (accum: ty) (fs: list (string*ty)) : ty :=
  match fs with
  | [] => accum
  | f::fs => struct_ty_aux (accum*f.2) fs
  end.

Definition struct_ty_prod fs : ty :=
  match fs with
  | [] => unitT
  | f::fs => struct_ty_aux f.2 fs
  end.

Definition structTy (d:descriptor) : ty :=
  struct_ty_prod d.(fields).

Definition structRefTy (d:descriptor) : ty :=
  structRefT (flatten_ty (structTy d)).

Fixpoint load_ty (t:ty): val :=
  match t with
  | prodT t1 t2 => λ: "l", (load_ty t1 (Var "l"), load_ty t2 (Var "l" +ₗ[t1] #1))
  | _ => λ: "l", !(Var "l")
  end.

Definition loadStruct (d:descriptor) : val := load_ty (structTy d).

Fixpoint field_offset (fields: list (string*ty)) f0 : option (Z * ty) :=
  match fields with
  | nil => None
  | (f,t)::fs => if String.eqb f f0 then Some (0, t)
               else match field_offset fs f0 with
                    | Some (off, t') => Some (ty_size t + off, t')
                    | None => None
                    end
  end%Z.

Definition fieldPointer (d:descriptor) (f:string) (l:loc): loc :=
  match field_offset d.(fields) f with
  | Some (off, _) => l +ₗ off
  | None => null
  end.

Definition fieldType (d:descriptor) (f:string): ty :=
  match field_offset d.(fields) f with
  | Some (_, t) => t
  | None => unitT
  end.

(** structFieldRef gives a function that takes a location and constant pointer
arithmetic on it (which is pre-computed based on the field and descriptor). *)
Definition structFieldRef (d:descriptor) (f:string): val :=
  match field_offset d.(fields) f with
  | Some (off, _) => λ: "p", (Var "p" +ₗ #off)
  | None => λ: "p", Var "p"
  end.


Definition loadField (d:descriptor) (f:string) : val :=
  match field_offset d.(fields) f with
  | Some (off, t) => λ: "p", load_ty t (Var "p" +ₗ #off)
  | None => λ: <>, #()
  end.

(* TODO: fix this to not be a macro *)
Fixpoint store_ty (t:ty) : val :=
  match t with
  | prodT t1 t2 => λ: "p" "v",
                  store_ty t1 (Var "p") (Fst (Var "v"));;
                  store_ty t2 (Var "p" +ₗ[t1] #1) (Snd (Var "v"))
  | _ => λ: "p" "v", Var "p" <- Var "v"
  end.

Definition storeStruct (d: descriptor) : val := store_ty (structTy d).

Definition storeField d f : val :=
  match field_offset d.(fields) f with
  | Some (off, t) => λ: "p" "x", store_ty t (Var "p" +ₗ #off) (Var "x")
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

Theorem ty_size_gt_0 : forall t, (0 < ty_size t)%Z.
Proof.
  induction t; simpl; lia.
Qed.

Theorem ty_size_length t : Z.to_nat (ty_size t) = length (flatten_ty t).
Proof.
  induction t; simpl; auto.
  pose proof (ty_size_gt_0 t1).
  pose proof (ty_size_gt_0 t2).
  rewrite app_length; auto.
  rewrite Z2Nat.inj_add; lia.

Qed.

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
  induction t; simpl; intros; eauto;
     try solve [ typecheck ].
  type_step.
  type_step.
  - econstructor.
    + eapply struct_weaken_hasTy.
      constructor.
      reflexivity.
    + eapply context_extension; intros; eauto.
      admit. (* this seems fishy; shouldn't matter if Γ binds "l" because
      load_ty is closed... *)
  - econstructor.
    + admit. (* TODO: not enough typing rules to do this *)
      (* eapply struct_offset_op_hasTy_eq; eauto.
      constructor.
      reflexivity. *)
    + autorewrite with ty.
      eapply context_extension; intros; eauto.
      admit.
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

Lemma flatten_ty_struct_prod fs : forall  a f,
  flatten_ty (struct_ty_aux (f * a) fs) =
  flatten_ty f ++ flatten_ty (struct_ty_aux a fs).
Proof.
  induction fs; intros.
  - simpl; auto.
  - rewrite ?IHfs.
    simpl.
    rewrite <- app_assoc; auto.
Qed.

Theorem flatten_ty_struct_aux fs : forall t,
  flatten_ty (struct_ty_aux t fs) = flatten_ty t ++ match fs with
                                                    | [] => []
                                                    | f::fs => flatten_ty (struct_ty_aux f.2 fs)
                                                    end.
Proof.
  destruct fs; simpl; intros.
  - rewrite app_nil_r; auto.
  - rewrite flatten_ty_struct_prod; auto.
Qed.

Theorem fieldOffset_t Γ fs f z t e :
  field_offset fs f = Some (z, t) ->
  Γ ⊢ e : structRefT (flatten_ty (struct_ty_prod fs)) ->
  Γ ⊢ (e +ₗ #z) : structRefT (flatten_ty t).
Proof using Type.
  revert e z t.
  induction fs; simpl; intros.
  - congruence.
  - destruct a as [f' t']; simpl in H0.
    destruct (f' =? f)%string.
    + inversion H; subst; clear H.
      apply struct_offset_0_hasTy.
      rewrite flatten_ty_struct_aux in H0.
      eapply struct_weaken_hasTy; eauto.
    + destruct_with_eqn (field_offset fs f); try congruence.
      destruct p as [off t''].
      inversion H; subst; clear H.

      apply struct_offset_op_collapse_hasTy; auto.
      eapply IHfs; eauto.

      eapply struct_offset_op_hasTy_eq; eauto.
      rewrite flatten_ty_struct_aux.
      autorewrite with ty.
      destruct fs; simpl in *; congruence.
Qed.

Theorem loadField_t : forall d f t z,
  field_offset d.(fields) f = Some (z, t) ->
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
  field_offset d.(fields) f = Some (z, t) ->
  Γ ⊢v structFieldRef d f : (structRefTy d -> structRefT (flatten_ty t)).
Proof.
  unfold structRefTy, structFieldRef.
  intros.
  rewrite H.
  type_step.
  eapply fieldOffset_t; eauto.
  typecheck.
Qed.

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
  induction t; simpl; intros; eauto.
  - typecheck.
  - type_step.
    type_step.
    type_step.
    + eapply app_hasTy; [ typecheck | ].
      eapply app_hasTy.
      { eapply struct_weaken_hasTy.
        typecheck. }
      eapply context_extension; intros; eauto.
      admit.
    + type_step.
      eapply app_hasTy; [ typecheck | ].
      type_step.
      * admit.
      * eapply context_extension; intros; eauto.
        admit.
  - typecheck.
  - typecheck.
  - typecheck.
  - typecheck.
  - typecheck.
  - typecheck.
    Fail idtac.
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
  field_offset d.(fields) f = Some (z, t) ->
  Γ ⊢v storeField d f : (structRefTy d -> t -> unitT).
Proof.
  unfold storeField; intros.
  rewrite H.
  type_step.
  type_step.
  eapply app_hasTy; [ typecheck | ].
  eapply app_hasTy.
  { eapply fieldOffset_t; eauto. }
  apply store_ty_t; eauto.
Qed.

End goose_lang.

Declare Reduction getField := cbv [getField rev fst snd app getField_e fields String.eqb Ascii.eqb eqb].

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
  (** Computes the address of field f given a base address for a struct of type d;
produces fieldPointer if the field exists and an error otherwise. *)
  Notation fieldPointer d f l :=
    (ltac:(let e := (eval cbv in (field_offset d.(fields) f)) in
           match e with
           | Some _ => exact (fieldPointer d f l)
           | None => fail "non-existent field" f
           end)) (only parsing).
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
