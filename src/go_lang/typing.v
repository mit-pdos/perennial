From Perennial.go_lang Require Import lang notation.

Inductive ty :=
| intT
| byteT
| boolT
| unitT
| prodT (t1 t2: ty)
| sumT (t1 t2: ty)
| arrowT (t1 t2: ty)
| refT (t: ty)
.

Infix "*" := prodT : heap_type.
Infix "->" := arrowT : heap_type.

Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).
Reserved Notation "Γ '⊢v' v : A" (at level 74, v, A at next level).

Definition Ctx := string -> option ty.
Instance empty_ctx : Empty Ctx := fun _ => None.
Instance ctx_insert : Insert binder ty Ctx.
Proof.
  hnf.
  exact (fun b t => match b with
                 | BNamed x => fun Γ =>
                                fun x' => if String.eqb x x'
                                       then Some t
                                       else Γ x'
                 | BAnon => fun Γ => Γ
                 end).
Defined.
Instance ctx_lookup : Lookup string ty Ctx := fun x Γ => Γ x.

Class ext_types (ext:ext_op) :=
  { get_ext_tys: external -> ty * ty; (* the argument type and return type *)
  }.

Section go_lang.
  Context `{ext_ty: ext_types}.

  Fixpoint zero_val (t:ty) : val :=
    match t with
    | intT => #0
    | byteT => #(LitByte 0)
    | boolT => #false
    | unitT => #()
    | prodT t1 t2 => (zero_val t1, zero_val t2)
    | sumT t1 t2 => InjLV (zero_val t1)
    | arrowT t1 t2 => λ: "x", zero_val t2
    | refT t => #null
    end.

  Inductive base_lit_hasTy : base_lit -> ty -> Prop :=
  | int_hasTy x : base_lit_hasTy (LitInt x) intT
  | byte_hasTy x : base_lit_hasTy (LitByte x) byteT
  | bool_hasTy x : base_lit_hasTy (LitBool x) boolT
  | unit_hasTy : base_lit_hasTy (LitUnit) unitT
  (* hmm seems like locs need to track the type they came from or the
  type-checking doesn't really work *)
  (* maybe we don't need a rule for locs at all? *)
  | loc_hasT t l : base_lit_hasTy (LitLoc l) (refT t)
  .

  Definition bin_op_ty (op:bin_op) : option (ty * ty * ty) :=
    match op with
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp => Some (intT, intT, intT)
    | LtOp | LeOp => Some (intT, intT, boolT)
    | _ => None
    end.

  Inductive expr_hasTy (Γ: Ctx) : expr -> ty -> Prop :=
  | var_hasTy x t :
      Γ !! x = Some t ->
      Γ ⊢ Var x : t
  | app_hasTy f x t1 t2 :
      Γ ⊢ x : t1 ->
      Γ ⊢ f : arrowT t1 t2 ->
      Γ ⊢ App f x : t2
  | val_expr_hasTy v t :
      val_hasTy Γ v t ->
      Γ ⊢ Val v : t
  | rec_expr_hasTy f x e t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e : t2 ->
      Γ ⊢ Rec f x e : arrowT t1 t2
  | panic_expr_hasTy msg t :
      Γ ⊢ Panic msg : t
  | offset_op_hasTy e1 e2 t :
      Γ ⊢ e1 : refT t ->
      Γ ⊢ e2 : intT ->
      Γ ⊢ BinOp OffsetOp e1 e2 : refT t
  | eq_op_hasTy e1 e2 t :
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      Γ ⊢ BinOp EqOp e1 e2 : boolT
  | bin_op_hasTy op e1 e2 t1 t2 t :
      bin_op_ty op = Some (t1, t2, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ BinOp op e1 e2 : t
  | pair_hasTy e1 e2 t1 t2 :
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ Pair e1 e2 : prodT t1 t2
  | fst_hasTy e t1 t2 :
      Γ ⊢ e : prodT t1 t2 ->
      Γ ⊢ Fst e : t1
  | snd_hasTy e t1 t2 :
      Γ ⊢ e : prodT t1 t2 ->
      Γ ⊢ Snd e : t2
  | inl_hasTy e t1 t2 :
      Γ ⊢ e : t1 ->
      Γ ⊢ InjL e : sumT t1 t2
  | inr_hasTy e t1 t2 :
      Γ ⊢ e : t2 ->
      Γ ⊢ InjR e : sumT t1 t2
  | case_hasTy cond e1 e2 t1 t2 t :
      Γ ⊢ cond : sumT t1 t2 ->
      Γ ⊢ e1 : arrowT t1 t ->
      Γ ⊢ e2 : arrowT t2 t ->
      Γ ⊢ Case cond e1 e2 : t
  | if_hasTy cond e1 e2 t :
      Γ ⊢ cond : boolT ->
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      Γ ⊢ If cond e1 e2 : t
  | alloc_hasTy n v t :
      Γ ⊢ n : intT ->
      Γ ⊢ v : t ->
      Γ ⊢ AllocN n v : refT t
  | load_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ Load l : t
  | store_hasTy l v t :
      Γ ⊢ l : refT t ->
      Γ ⊢ v : t ->
      Γ ⊢ Store l v : unitT
  | external_hasTy op e t1 t2 :
      get_ext_tys op = (t1, t2) ->
      Γ ⊢ e : t1 ->
      Γ ⊢ ExternalOp op e : t2
  | encode_hasTy n p :
      Γ ⊢ n : intT ->
      Γ ⊢ p : refT byteT ->
      Γ ⊢ EncodeInt n p : unitT
  | decode_hasTy p :
      Γ ⊢ p : refT byteT ->
      Γ ⊢ DecodeInt p : intT
  where "Γ ⊢ e : A" := (expr_hasTy Γ e A)
  with val_hasTy (Γ: Ctx) : val -> ty -> Prop :=
  | val_base_lit_hasTy v t :
      base_lit_hasTy v t -> val_hasTy Γ (LitV v) t
  | val_pair_hasTy v1 v2 t1 t2 :
      Γ ⊢v v1 : t1 ->
      Γ ⊢v v2 : t2 ->
      Γ ⊢v PairV v1 v2 : prodT t1 t2
  | val_injL_hasTy v1 t1 t2 :
      Γ ⊢v v1 : t1 ->
      Γ ⊢v InjLV v1 : sumT t1 t2
  | val_injR_hasTy v2 t1 t2 :
      Γ ⊢v v2 : t2 ->
      Γ ⊢v InjRV v2 : sumT t1 t2
  | rec_val_hasTy f x e t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ⊢ e : t2 ->
      Γ ⊢v RecV f x e : arrowT t1 t2
  where "Γ ⊢v v : A" := (val_hasTy Γ v A)
  .

  Hint Constructors expr_hasTy val_hasTy base_lit_hasTy.

  Theorem zero_val_ty ty Γ :
    Γ ⊢v zero_val ty : ty.
  Proof.
    generalize dependent Γ.
    induction ty; simpl; eauto.
    repeat econstructor.
  Qed.

  Lemma extend_context_add:
    ∀ Γ Γ' : string → option ty,
      (∀ (x : string) (t0 : ty), Γ x = Some t0 → Γ' x = Some t0)
      → ∀ (x : binder) (t: ty) (x0 : string) (t0 : ty),
        (<[x:=t]> Γ) x0 = Some t0
        → (<[x:=t]> Γ') x0 = Some t0.
  Proof.
    intros Γ Γ' Heq f t x t0 HΓ.
    unfold insert, ctx_insert in *.
    destruct f; eauto.
    destruct (s =? x)%string; eauto.
  Qed.

  Hint Resolve extend_context_add.
  Ltac inv H := inversion H; subst; clear H.

  Theorem context_extension Γ Γ' (t: ty) : forall e,
      (forall x t0, Γ x = Some t0 -> Γ' x = Some t0) ->
      Γ ⊢ e : t ->
      Γ' ⊢ e : t
    with val_context_extension Γ Γ' (t: ty) : forall v,
        (forall x t0, Γ x = Some t0 -> Γ' x = Some t0) ->
        Γ ⊢v v : t ->
        Γ' ⊢v v : t.
  Proof.
    - intros e Heq Hty; inv Hty; try solve [ (repeat econstructor); eauto ].
    - intros v Heq Hty; inv Hty; try solve [ (repeat econstructor); eauto ].
  Abort.

  Theorem rec_expr_hasTy_eq t1 t2 Γ Γ' f x e :
    Γ' = (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ->
    Γ' ⊢ e : t2 ->
    Γ ⊢ Rec f x e : arrowT t1 t2.
  Proof.
    intros; subst; eauto.
  Qed.

  Inductive type_annot :=
  | annot (e:string) (t:ty).

  Definition annot_e a := let 'annot e _  := a in e.

End go_lang.

Notation "v :: t" := (annot v t) (only printing) : expr_scope.
Coercion annot_e : type_annot >-> string.

Delimit Scope heap_types with T.
Delimit Scope heap_type with ht.
Bind Scope heap_type with ty.

Notation "Γ ⊢ e : A" := (expr_hasTy Γ%ht e A%ht) : heap_types.
Notation "Γ ⊢v v : A" := (val_hasTy Γ%ht v A%ht) : heap_types.
Notation "⊢ v : A" := (base_lit_hasTy v%V A%ht) (at level 90, only printing) : heap_types.
Notation "⊢ e : A" := (expr_hasTy ∅ e%E A%ht) (at level 90, e at next level, A at next level) : heap_types.

Theorem insert_anon t : (<[BAnon := t]> : Ctx -> Ctx) = (fun Γ => Γ).
Proof.
  reflexivity.
Qed.

Hint Constructors expr_hasTy : types.
Hint Constructors val_hasTy : types.
Hint Constructors base_lit_hasTy : types.

Local Ltac simp := unfold For; simpl; rewrite ?insert_anon.
Ltac type_step :=
  match goal with
  | [ |- expr_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- expr_hasTy _ _ _ ] => econstructor
  | [ |- expr_hasTy _ (Rec _ (annot_e (annot _ ?t)) _) (arrowT _ _) ] => eapply (rec_expr_hasTy_eq t)
  | [ |- expr_hasTy _ (Rec _ _ _) (arrowT _ _) ] => eapply rec_expr_hasTy_eq
  | [ |- val_hasTy _ _ _ ] => solve [eauto with types] || econstructor
  | [ |- base_lit_hasTy _ _ ] => solve [eauto with types] || econstructor
  end; simp.

Ltac typecheck :=
  repeat (type_step; try match goal with
                         | [ |- _ = _ ] => cbv; reflexivity
                         end).
