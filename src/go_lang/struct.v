From Perennial.go_lang Require Export lang.
From Perennial.go_lang Require Import notation.
From Perennial.go_lang Require Import typing.

(** * Lightweight struct library

    Access field offsets within pairs by name rather than using Fst and Snd. *)

Record descriptor :=
  mkStruct { fields: list (string*ty); }.

(* Check eq_refl : (#0, #1, #2)%E = ((#0, #1), #2)%E. *)

Section go_lang.
  Context `{ffi_sem: ext_semantics}.

Fixpoint getField_e (f0: string) (rev_fields: list (string*ty)) (se: expr): expr :=
  match rev_fields with
  | [] => LitV LitUnit
  | [f] => if String.eqb (fst f) f0 then se else #()
  | f::fs => if String.eqb (fst f) f0 then Snd se else getField_e f0 fs (Fst se)
  end.

Definition getField (d:descriptor) f : val :=
  λ: "v", getField_e f (rev d.(fields)) (Var "v").

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

Definition allocStruct (d:descriptor) (fvs: list (string*expr)) : expr :=
  match build_struct_val fvs (rev d.(fields)) with
  | Some v => AllocStruct v
  | None => LitV LitUnit
  end.

Fixpoint struct_ty_prod (rev_fields: list (string*ty)) : ty :=
  match rev_fields with
  | nil => unitT
  | [f] => snd f
  | f::fs => struct_ty_prod fs * snd f
  end.

Definition structTy (d:descriptor) : ty :=
  struct_ty_prod (rev (fields d)).

Definition structRefTy (d:descriptor) : ty :=
  structRefT (flatten_ty (structTy d)).

Fixpoint ty_size (t:ty) : Z :=
  match t with
  | prodT t1 t2 => ty_size t1 + ty_size t2
  (* this gives unit values space, which seems fine *)
  | _ => 1
  end.

Fixpoint load_ty (t:ty) (e:expr) : expr :=
  match t with
  | prodT t1 t2 => (load_ty t1 e, load_ty t2 (e +ₗ #(ty_size t1)))
  | _ => !e
  end.

Definition loadStruct (d:descriptor) : val :=
  λ: "p", load_ty (structTy d) (Var "p").

Fixpoint field_offset (fields: list (string*ty)) f0 : option (Z * ty) :=
  match fields with
  | nil => None
  | (f,t)::fs => if String.eqb f f0 then Some (0, t)
               else match field_offset fs f0 with
                    | Some (off, t') => Some (ty_size t + off, t')
                    | None => None
                    end
  end%Z.

Definition loadField (d:descriptor) (f:string) : val :=
  match field_offset d.(fields) f with
  | Some (off, t) => λ: "p", load_ty t (Var "p" +ₗ #off)
  | None => λ: <>, #()
  end.

(* TODO: implement these, ideally while re-using infrastructure for loadField
(although storing is more complicated since it requires traversing through
struct and the value being assigned) *)
Fixpoint store_ty (t:ty) (e:expr) (v:expr) : expr :=
  match t with
  | prodT t1 t2 => store_ty t1 e (Fst v);;
                  store_ty t2 (e +ₗ #(ty_size t1)) (Snd v)
  | _ => e <- v
  end.

Definition storeStruct d : val :=
  λ: "p" "x", store_ty (structTy d) (Var "p") (Var "x").

Definition storeField d f : val :=
  match field_offset d.(fields) f with
  | Some (off, t) => λ: "p" "x", store_ty t (Var "p" +ₗ #off) (Var "x")
  | None => λ: <> <>, #()
  end.

Context {ext_ty: ext_types ext}.
Set Default Proof Using "ext ext_ty".

Hint Resolve struct_offset_op_hasTy_eq : types.

Local Open Scope heap_types.

Theorem load_struct_ref_hasTy Γ l t ts :
  Γ ⊢ l : structRefT (t::ts) ->
  Γ ⊢ !l : t.
Proof.
  intros.
  apply load_hasTy.
  apply struct_singleton_hasTy.
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

Theorem ty_size_gt_0 : forall t, (0 <= ty_size t)%Z.
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

Hint Resolve load_hasTy struct_singleton_hasTy.

Hint Rewrite @drop_app : ty.

Theorem load_ty_t : forall Γ t e,
  Γ ⊢ e : structRefT (flatten_ty t) ->
  Γ ⊢ load_ty t e : t.
Proof.
  induction t; simpl; intros; eauto.
  econstructor.
  - apply IHt1.
    eauto using struct_weaken_hasTy.
  - apply IHt2.
    eapply struct_offset_op_hasTy_eq; eauto.
    autorewrite with ty; auto.
Qed.

Theorem loadStruct_hasTy Γ d :
  Γ ⊢v loadStruct d : (structRefTy d -> structTy d).
Proof.
  unfold loadStruct, structRefTy, structTy.
  econstructor.
  rewrite insert_anon.
  apply load_ty_t.
  constructor; auto.
Qed.

Theorem concat_fields_cons_eq f fs :
  concat (map (λ ft : string * ty, flatten_ty ft.2) (f::fs)) =
  flatten_ty (struct_ty_prod (rev (f::fs))).
Proof.
  revert f.
  induction fs; intros.
  - simpl. rewrite app_nil_r; auto.
  - change (concat (map (λ ft : string * ty, flatten_ty ft.2) (f :: a :: fs)))
      with (flatten_ty f.2 ++ concat (map (λ ft : string * ty, flatten_ty ft.2) (a :: fs))).
    rewrite IHfs.
Admitted.

Theorem concat_fields_eq f x fs :
  field_offset fs f = Some x ->
  concat (map (λ ft : string * ty, flatten_ty ft.2) fs) =
  flatten_ty (struct_ty_prod (rev fs)).
Proof.
  destruct fs; intros.
  - simpl in H; congruence.
  - apply concat_fields_cons_eq.
Qed.

Theorem fieldOffset_t Γ fs f z t e :
  field_offset fs f = Some (z, t) ->
  Γ ⊢ e : structRefT (flatten_ty (struct_ty_prod (rev fs))) ->
  Γ ⊢ (e +ₗ #z) : structRefT (flatten_ty t).
Proof.
  intros.
  erewrite <- concat_fields_eq in H0 by eauto.
  generalize dependent e.
  generalize dependent z.
  generalize dependent t.
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
      assert (Γ ⊢ e +ₗ #(ty_size t') : structRefT (concat (map (λ ft : string * ty, flatten_ty ft.2) fs))).
      { eapply struct_offset_op_hasTy_eq; eauto.
        autorewrite with ty; auto. }
      eapply IHfs in H; eauto.
      apply struct_offset_op_collapse_hasTy; auto.
Qed.

Theorem loadField_t : forall d f t z,
  field_offset d.(fields) f = Some (z, t) ->
  forall Γ, (Γ ⊢ loadField d f : (structRefTy d -> t))%T.
Proof.
  unfold structRefTy, loadField; simpl.
  intros.
  rewrite H; simpl.
  econstructor.
  econstructor.
  eapply load_ty_t.
  eapply fieldOffset_t; eauto.
  econstructor; auto.
Qed.

Hint Constructors expr_hasTy.

Theorem store_ty_t : forall Γ t e v,
  Γ ⊢ e : structRefT (flatten_ty t) ->
  Γ ⊢ v : t ->
  Γ ⊢ store_ty t e v : unitT.
Proof.
  induction t; simpl; intros; eauto.
  econstructor.
  - apply IHt1; eauto.
  - econstructor; rewrite ?insert_anon.
    apply IHt2; eauto.
    eapply struct_offset_op_hasTy_eq; eauto.
    autorewrite with ty; auto.
Qed.

Theorem storeStruct_t : forall Γ d p e,
  Γ ⊢ p : structRefTy d ->
  Γ ⊢ e : structTy d ->
  Γ ⊢ storeStruct d p e : unitT.
Proof.
  unfold structRefTy, storeStruct; intros.
  repeat (econstructor; rewrite ?insert_anon; eauto).
  apply store_ty_t; eauto.
Qed.

Theorem storeField_t : forall Γ d f p v z t,
  field_offset d.(fields) f = Some (z, t) ->
  Γ ⊢ p : structRefTy d ->
  Γ ⊢ v : t ->
  Γ ⊢ storeField d f p v : unitT.
Proof.
  unfold storeField; intros.
  rewrite H.
  repeat (econstructor; rewrite ?insert_anon; eauto).
  apply store_ty_t; eauto.
  eapply fieldOffset_t; eauto.
Qed.

End go_lang.

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
  Notation new := allocStruct.
  Notation get := getField.
  (* TODO: load/loadF could probably use better names *)
  Notation load := loadStruct.
  Notation loadF := loadField.
  Notation t := structTy.
  Notation ptrT := structRefTy.
  Notation store := storeStruct.
  Notation storeF := storeField.
End struct.

Notation "'structF!' desc fname" := (ltac:(make_structF desc fname))
                                    (at level 0, desc, fname at next level, only parsing).

Notation "f :: t" := (@pair string ty f%string t%ht).
Notation "f ::= v" := (@pair string expr f%string v%E) (at level 60) : expr_scope.
