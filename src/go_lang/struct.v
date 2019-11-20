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

Fixpoint fieldTypes (fields: list (string*ty)) : list ty :=
  match fields with
  | [] => []
  | (_,t)::fs => flatten_ty t ++ fieldTypes fs
  end.

Definition structRefTy (d:descriptor) : ty :=
  structRefT (fieldTypes d.(fields)).

Fixpoint ty_size (t:ty) : Z :=
  match t with
  | prodT t1 t2 => ty_size t1 + ty_size t2
  (* this gives unit values space, which seems fine *)
  | _ => 1
  end.

Fixpoint load_ty (t:ty) (e:expr) (off:Z) : expr :=
  match t with
  | prodT t1 t2 => (load_ty t1 e off, load_ty t2 e (off + ty_size t1))
  | _ => !(e +ₗ #off)
  end.

Definition loadStruct (d:descriptor) : val :=
  λ: "p", load_ty (structTy d) (Var "p") 0.

Fixpoint field_offset (fields: list (string*ty)) f0 : (Z * ty) :=
  match fields with
  | nil => (-1, unitT)
  | f::fs => if String.eqb (fst f) f0 then (0, snd f)
           else let (off, t) := field_offset fs f0 in
                (ty_size (snd f) + off, t)
  end%Z.

Definition loadField (d:descriptor) (f:string) : val :=
  let (off, t) := field_offset d.(fields) f in
  λ: "p", load_ty t (Var "p") off.

Fixpoint fieldTy (fs:list (string*ty)) (f0: string) : option ty :=
  match fs with
  | [] => None
  | (f,t)::fs => if String.eqb f f0 then Some t else fieldTy fs f0
  end.

(* TODO: implement these, ideally while re-using infrastructure for loadField
(although storing is more complicated since it requires traversing through
struct and the value being assigned) *)
Axiom storeStruct : descriptor -> val.
Axiom storeField : descriptor -> string -> val.

Context {ext_ty: ext_types ext}.
Set Default Proof Using "ext ext_ty".

Hint Resolve struct_offset_op_hasTy_eq : types.

Theorem load_structRef_off : forall Γ e ts n t,
  ts !! Z.to_nat n = Some t ->
  (Γ ⊢ e : structRefT ts)%T ->
  (Γ ⊢ ! (e +ₗ #n) : t)%T.
Proof.
  intros.
  destruct (elem_of_list_split_length ts (Z.to_nat n) t)
    as [l1 [l2 (?&?)]]; auto; subst.
  eapply load_struct_hasTy.
  eapply struct_offset_op_hasTy_eq; eauto.
  rewrite drop_app_alt; auto.
Qed.

Hint Resolve load_structRef_off : types.

Theorem take_1_drop_is_lookup n : forall A (l: list A) x,
  take 1 (drop n l) = [x] ->
  l !! n = Some x.
Proof.
  induction n; destruct l; simpl in *; auto; intros; try congruence.
Qed.

Hint Resolve take_1_drop_is_lookup : types.

Lemma take_app_take1:
  ∀ l1 l2 ts' : list ty,
  take (strings.length l1 + strings.length l2) ts' = l1 ++ l2 ->
  take (strings.length l1) ts' = l1.
Proof.
  intros l1 l2 ts' H.
  replace (take (strings.length l1) ts') with (take (strings.length l1) (take (strings.length l1 + strings.length l2) ts')).
  - rewrite H.
    rewrite take_app; auto.
  - rewrite take_take.
    rewrite Min.min_l; try lia; auto.
Qed.

Theorem ty_size_flatten t : ty_size t = length (flatten_ty t).
Proof.
  induction t; simpl; auto.
  rewrite app_length; auto.
  lia.
Qed.

Lemma take_app_drop1:
  ∀ (ts l1 l2 : list ty) (n' : nat),
  take (strings.length l1 + strings.length l2) (drop n' ts) = l1 ++ l2
  → take (strings.length l2) (drop (n' + strings.length l1) ts) = l2.
Proof.
  intros ts l1 l2 n' H.
  rewrite <- drop_drop.
  rewrite take_drop_commute.
  rewrite H.
  rewrite drop_app; auto.
Qed.

Theorem ty_size_gt_0 : forall t, (0 <= ty_size t)%Z.
Proof.
  induction t; simpl; lia.
Qed.

Theorem load_ty_t : forall Γ t ts n,
  (0 <= n)%Z ->
  firstn (length (flatten_ty t)) (drop (Z.to_nat n) ts) = flatten_ty t ->
  (Γ ⊢ (λ: "p", load_ty t (Var "p") n)%V : (structRefT ts -> t))%T.
Proof.
  intros.
  apply empty_context_to_any.
  constructor.
  constructor.
  rewrite insert_anon.
  generalize dependent n.
  generalize dependent ts.
  induction t; simpl; intros;
    eauto with types.
  rewrite app_length in H0.
  constructor.
  - apply IHt1; auto.
    eapply take_app_take1; eauto.
  - apply IHt2; auto.
    pose proof (ty_size_gt_0 t1); lia.
    rewrite ty_size_flatten.
    generalize dependent (flatten_ty t1); intros l1 **.
    generalize dependent (flatten_ty t2); intros l2 **.
    replace (Z.to_nat (n + length l1)) with (Z.to_nat n + length l1)%nat.
    eapply take_app_drop1; eauto.
    (* [lia] doesn't solve this goal on its own in Coq 8.9 *)
    rewrite ?Z2Nat.inj_add ?Nat2Z.id; lia.
Qed.

Theorem field_offset1_gt_0 : forall fs f t,
  fieldTy fs f = Some t ->
  (0 <= (field_offset fs f).1)%Z.
Proof.
  induction fs; simpl; intros; eauto.
  - congruence.
  - destruct a as [f0 t']; simpl.
    destruct (f0 =? f)%string; simpl in *; try lia.
    + destruct_with_eqn (field_offset fs f).
      eapply IHfs in H.
      rewrite Heqp in H; simpl in *.
      pose proof (ty_size_gt_0 t').
      lia.
Qed.

Theorem field_offset_to_fieldTy : forall fs f z t0 t,
  fieldTy fs f = Some t0 ->
  field_offset fs f = (z, t) ->
  t = t0 /\
  exists ts1 ts2, fieldTypes fs = ts1 ++ flatten_ty t ++ ts2 /\
             length ts1 = Z.to_nat z.
Proof.
  induction fs; simpl; intros.
  - congruence.
  - destruct a as [f0 t']; simpl in *.
    destruct (f0 =? f)%string.
    + inversion H0; subst; clear H0.
      inversion H; subst; clear H.
      intuition.
      eexists nil, _; simpl; eauto.
    + destruct_with_eqn (field_offset fs f).
      inversion H0; subst; clear H0.
      pose proof (IHfs _ _ _ _ H Heqp); intuition subst.
      destruct H2 as (ts1&ts2&?&?).
      rewrite H0.
      eexists (flatten_ty t' ++ ts1), _; intuition eauto.
      rewrite <- app_assoc; auto.
      rewrite app_length.
      rewrite ty_size_flatten.
      rewrite H1.
      pose proof (field_offset1_gt_0 fs f t0); intuition.
      rewrite Heqp in H3; simpl in *.
      (* [lia] doesn't solve this goal on its own in Coq 8.9 *)
      rewrite ?Z2Nat.inj_add ?Nat2Z.id; lia.
Qed.

Theorem loadField_t : forall d f t,
  fieldTy d.(fields) f = Some t ->
  forall Γ, (Γ ⊢ loadField d f : (structRefTy d -> t))%T.
Proof.
  destruct d as [fs].
  unfold structRefTy, loadField; simpl.
  intros.
  destruct_with_eqn (field_offset fs f).
  pose proof (field_offset_to_fieldTy _ _ _ _ _ H Heqp);
    intuition subst.
  destruct H2 as (t1&t2&?&?).
  rewrite H0.
  eapply load_ty_t.
  pose proof (field_offset1_gt_0 fs f t); intuition.
  { rewrite Heqp in H3; simpl in *; lia. }
  rewrite drop_app_alt; [ | lia ].
  rewrite take_app; auto.
Qed.

Theorem storeStruct_t : forall Γ d p e,
  (Γ ⊢ p : structRefTy d ->
   Γ ⊢ e : structTy d ->
   Γ ⊢ storeStruct d p e : unitT)%T.
Proof.
Abort.

Theorem storeField_t : forall Γ d f p v t,
  fieldTy d.(fields) f = Some t ->
  (Γ ⊢ p : structRefTy d ->
   Γ ⊢ v : t ->
   Γ ⊢ storeField d f p v : unitT)%T.
Proof.
Abort.

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
