From Perennial.goose_lang Require Import notation.
From Perennial.new_goose_lang Require Import typing.

Reserved Notation "![ t ] e"
         (at level 9, right associativity, format "![ t ]  e").
Reserved Notation "e1 <-[ t ] e2"
         (at level 80, format "e1  <-[ t ]  e2").

Section goose_lang.
  Context `{ffi_syntax}.

  (** allocation with a type annotation *)
  Definition ref_to (t:go_type): val := λ: "v", ref (Var "v").
  Definition ref_zero (t:go_type): val := λ: <>, ref (zero_val t).

  Inductive go_abstract_type :=
  | cellT
  | unitT
  | prodT (t1 t2 : go_abstract_type)
  .
  Local Fixpoint go_abstract_type_size (t : go_abstract_type) : Z :=
    match t with
    | prodT t1 t2 => go_abstract_type_size t1 + go_abstract_type_size t2
    | cellT => 1
    | unitT => 0
    end.

  Local Fixpoint go_type_interp (t : go_type) : go_abstract_type :=
    match t with
    | sliceT _ => prodT cellT $ prodT cellT $ prodT cellT unitT
    | structT decls => fold_right prodT unitT (fmap (go_type_interp ∘ snd) decls)
    | interfaceT => prodT cellT $ prodT cellT$ prodT cellT unitT (* type id, val, methods *)
    | _ => cellT
    end.

  (* TODO: seal *)
  Definition load_ty (t : go_type) : val :=
    (fix load_ty_aux t : val :=
      match t with
      | prodT t1 t2 => (λ: "l", (load_ty_aux t1 (Var "l"),
                                  load_ty_aux t2 (Var "l" +ₗ #(go_abstract_type_size t1))))%V
      | cellT => (λ: "l", !(Var "l"))%V
      | unitT => (λ: <>, #())%V
      end) (go_type_interp t).

  Fixpoint store_ty t: val :=
    (fix store_ty_aux t : val :=
       match t with
       | prodT t1 t2 => (λ: "pv",
                         let: "p" := Fst (Var "pv") in
                         let: "v" := Snd (Var "pv") in
                         store_ty_aux t1 (Var "p", Fst (Var "v"));;
                         store_ty_aux t2 (Var "p" +ₗ #(go_abstract_type_size t1), Snd (Var "v")))%V
       | cellT => (λ: "pv", Fst (Var "pv") <- Snd (Var "pv"))%V
       | unitT => (λ: <>, #())%V
       end) (go_type_interp t).

  Definition ref_ty (t : go_type) : val := λ: "v", ref (Var "v").

  (* approximate types for closed values, as obligatons for using load_ty and
  store_ty *)

  Inductive val_ty : val → go_abstract_type → Prop :=
  | val_ty_pair v1 t1 v2 t2 : val_ty v1 t1 ->
                              val_ty v2 t2 ->
                              val_ty (PairV v1 v2) (prodT t1 t2)
  | unit_ty v : cell v -> val_ty v cellT
  | val_ty_cell v : cell v -> val_ty v cellT
  .

  Inductive val_ty : val -> ty -> Prop :=
  | base_ty l t : lit_ty l t -> val_ty (LitV l) t
  | val_ty_pair v1 t1 v2 t2 : val_ty v1 t1 ->
                              val_ty v2 t2 ->
                              val_ty (PairV v1 v2) (prodT t1 t2)
  | nil_ty t : val_ty (InjLV (LitV LitUnit)) (listT t)
  | sum_ty_l v1 t1 t2 : val_ty v1 t1 ->
                        val_ty (InjLV v1) (sumT t1 t2)
  | sum_ty_r v2 t1 t2 : val_ty v2 t2 ->
                        val_ty (InjRV v2) (sumT t1 t2)
  | map_def_ty v kt vt : val_ty v vt ->
                     val_ty (MapNilV v) (mapValT kt vt)
  | map_cons_ty k v mv' vt kt : val_ty mv' (mapValT kt vt) ->
                            val_ty k kt ->
                            val_ty v vt ->
                            val_ty (InjRV (k, v, mv')%V) (mapValT kt vt)
  | rec_ty f x e t1 t2 : val_ty (RecV f x e) (arrowT t1 t2)
  | ext_val_ty x T : val_ty (ExtV x) (extT T)
  .

  Ltac invc H := inversion H; subst; clear H.

  (* Prove that this is a sensible definition *)

  Theorem zero_val_ty' t : has_zero t -> val_ty (zero_val t) t.
  Proof.
    induction t; simpl; intros; intuition eauto using val_ty, lit_ty.
    destruct t; eauto using val_ty, lit_ty.
  Qed.

  Theorem val_ty_len {v t} :
    val_ty v t ->
    length (flatten_struct v) = Z.to_nat (ty_size t).
  Proof.
    induction 1; simpl; rewrite -> ?app_length in *; auto.
    - invc H; eauto.
    - pose proof (ty_size_ge_0 t1).
      pose proof (ty_size_ge_0 t2).
      lia.
  Qed.

  Theorem val_ty_flatten_length v t :
    val_ty v t ->
    length (flatten_struct v) = length (flatten_ty t).
  Proof.
    induction 1; simpl; auto.
    - invc H; eauto.
    - rewrite ?app_length.
      lia.
  Qed.

  Ltac inv_lit_ty :=
    try match goal with
        | [ H: lit_ty _ _ |- _ ] => solve [ inversion H ]
        end.

  Theorem flatten_struct_inj v1 v2 t :
    val_ty v1 t ->
    val_ty v2 t ->
    flatten_struct v1 = flatten_struct v2 ->
    v1 = v2.
  Proof.
    intros H.
    revert v2.
    induction H; simpl; intros.
    - inversion H0; subst; simpl in H1;
        try solve [ inversion H ];
        try (destruct l, l0; inversion H1; subst);
        auto.
    - invc H1; simpl in *; inv_lit_ty.
      pose proof (val_ty_len H6).
      pose proof (val_ty_len H).
      unshelve epose proof (app_inj_1 _ _ _ _ _ H2); first by congruence.
      intuition eauto.
      eapply IHval_ty1 in H5; eauto; subst.
      eapply IHval_ty2 in H8; eauto; subst.
      congruence.
    - invc H; simpl in *; inv_lit_ty; try congruence.
    - invc H0; simpl in *; inv_lit_ty; try congruence.
    - invc H0; simpl in *; inv_lit_ty; try congruence.
    - invc H0; simpl in *; inv_lit_ty; try congruence.
    - invc H; simpl in *; inv_lit_ty; try congruence.
      * invc H3. invc H2; simpl in *; inv_lit_ty; try congruence.
      * invc H3. invc H2; simpl in *; inv_lit_ty; try congruence.
    - invc H; simpl in *; inv_lit_ty; try congruence.
    - invc H; simpl in *; inv_lit_ty; try congruence.
  Qed.

End goose_lang.

#[global]
Hint Resolve zero_val_ty' : core.
(* give has_zero a chance to simplify, then eauto can keep going *)
#[global]
Hint Extern 50 (has_zero _) => progress simpl : core.
(* Only use constructors as fallback *)
#[global]
Hint Extern 10 (val_ty _ _) => constructor : core.
#[global]
Hint Extern 10 (lit_ty _ _) => constructor : core.
(* Just a compat alias *)
Ltac val_ty :=
  lazymatch goal with
  | |- val_ty _ _ => by eauto 20
  | |- lit_ty _ _ => by eauto
  | _ => fail "not a val_ty goal"
  end.

Notation "![ t ] e" := (load_ty t e%E) : expr_scope.
(* NOTE: in code we want to supply arbitrary expressions, so we have the usual
   notation, but the specs should be in terms of value pairs, so we have a
   similar notation in the value-scope (even though this is an expression and
   not a value)

   See the HeapLang documentation in Iris for par, which has a similar
   trick. *)
Notation "e1 <-[ t ] e2" := (store_ty t (Pair e1%E e2%E)) : expr_scope.
Notation "v1 <-[ t ] v2" := (store_ty t (PairV v1%V v2%V)) : val_scope.
