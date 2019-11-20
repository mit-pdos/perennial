From Perennial.go_lang Require Import lang notation.

Inductive ty :=
| uint64T
| uint32T
| byteT
| boolT
| unitT
| stringT
| prodT (t1 t2: ty)
| sumT (t1 t2: ty)
| arrowT (t1 t2: ty)
| refT (t: ty)
| structRefT (ts: list ty)
| mapValT (t: ty) (* keys are always uint64, for now *)
.

Definition mapT (vt:ty) : ty := refT (mapValT vt).

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
    | uint64T => #0
    | uint32T => #(U32 0)
    | byteT => #(LitByte 0)
    | boolT => #false
    | unitT => #()
    | stringT => #(str"")
    | mapValT vt => MapNilV (zero_val vt)
    | prodT t1 t2 => (zero_val t1, zero_val t2)
    | sumT t1 t2 => InjLV (zero_val t1)
    | arrowT t1 t2 => λ: <>, zero_val t2
    | refT t => #null
    | structRefT ts => #null
    end.

  Inductive base_lit_hasTy : base_lit -> ty -> Prop :=
  | uint64_hasTy x : base_lit_hasTy (LitInt x) uint64T
  | uint32_hasTy x : base_lit_hasTy (LitInt32 x) uint32T
  | byte_hasTy x : base_lit_hasTy (LitByte x) byteT
  | bool_hasTy x : base_lit_hasTy (LitBool x) boolT
  | unit_hasTy : base_lit_hasTy (LitUnit) unitT
  | string_hasTy s : base_lit_hasTy (LitString s) stringT
  (* to get a type for a location, the typing judgement should keep track of it
  from its allocation and then throughout the program; null is the only special
  case of a location value the programmer can directly and legally refer to *)
  | loc_null_hasTy t : base_lit_hasTy (LitLoc null) (refT t)
  | structRef_null_hasTy ts : base_lit_hasTy (LitLoc null) (structRefT ts)
  .

  Definition bin_op_ty (op:bin_op) (t:ty) : option (ty * ty * ty) :=
    match op with
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp => Some (t, t, t)
    | LtOp | LeOp => Some (t, t, boolT)
    | _ => None
    end.

  Definition un_op_ty (op:un_op) : option (ty * ty) :=
    match op with
    | NegOp => Some (boolT, boolT)
    | ToUInt64Op => Some (uint32T, uint64T)
    | _ => None
    end.

  Fixpoint flatten_ty (t: ty) : list ty :=
    match t with
    | prodT t1 t2 => flatten_ty t1 ++ flatten_ty t2
    | _ => [t]
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
  | un_op_hasTy op e1 t1 t :
      un_op_ty op = Some (t1, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ UnOp op e1 : t
  | offset_op_hasTy e1 e2 t :
      Γ ⊢ e1 : refT t ->
      Γ ⊢ e2 : uint64T ->
      Γ ⊢ BinOp OffsetOp e1 e2 : refT t
  | struct_offset_op_hasTy e1 (v: Z) ts :
      Γ ⊢ e1 : structRefT ts ->
      Γ ⊢ BinOp OffsetOp e1 #v : structRefT (skipn (Z.to_nat v) ts)
  | eq_op_hasTy e1 e2 t :
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      Γ ⊢ BinOp EqOp e1 e2 : boolT
  | bin_op_64_hasTy op e1 e2 t1 t2 t :
      bin_op_ty op uint64T = Some (t1, t2, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ BinOp op e1 e2 : t
  | bin_op_32_hasTy op e1 e2 t1 t2 t :
      bin_op_ty op uint32T = Some (t1, t2, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ e2 : t2 ->
      Γ ⊢ BinOp op e1 e2 : t
  | str_plus_hasTy e1 e2 :
      Γ ⊢ e1 : stringT ->
      Γ ⊢ e2 : stringT ->
      Γ ⊢ BinOp PlusOp e1 e2 : stringT
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
      Γ ⊢ n : uint64T ->
      Γ ⊢ v : t ->
      Γ ⊢ AllocN n v : refT t
  | alloc_struct_hasTy v t :
      Γ ⊢ v : t ->
      Γ ⊢ AllocStruct v : structRefT (flatten_ty t)
  | load_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ Load l : t
  | load_struct_hasTy l t ts :
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ Load l : t
  | store_hasTy l v t :
      Γ ⊢ l : refT t ->
      Γ ⊢ v : t ->
      Γ ⊢ Store l v : unitT
  | store_struct_hasTy l v t ts :
      Γ ⊢ l : structRefT ts ->
      Γ ⊢ v : t ->
      flatten_ty t = ts ->
      Γ ⊢ Store l v : unitT
  | external_hasTy op e t1 t2 :
      get_ext_tys op = (t1, t2) ->
      Γ ⊢ e : t1 ->
      Γ ⊢ ExternalOp op e : t2
  | mapGet_hasTy m k vt :
      Γ ⊢ m : mapT vt ->
      Γ ⊢ k : uint64T ->
      Γ ⊢ MapGet m k : prodT vt boolT
  | mapInsert_hasTy m k v vt :
      Γ ⊢ m : mapT vt ->
      Γ ⊢ k : uint64T ->
      Γ ⊢ v : vt ->
      Γ ⊢ MapInsert m k v : unitT
  | encode_hasTy n p :
      Γ ⊢ n : uint64T ->
      Γ ⊢ p : refT byteT ->
      Γ ⊢ EncodeInt n p : unitT
  | decode_hasTy p :
      Γ ⊢ p : refT byteT ->
      Γ ⊢ DecodeInt p : uint64T
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
  | mapNil_hasTy v t :
      Γ ⊢v v : t ->
      Γ ⊢v MapNilV v : mapValT t
  where "Γ ⊢v v : A" := (val_hasTy Γ v A)
  .

  Hint Constructors expr_hasTy val_hasTy base_lit_hasTy.

  Theorem zero_val_ty ty Γ :
    Γ ⊢v zero_val ty : ty.
  Proof.
    generalize dependent Γ.
    induction ty; simpl; eauto.
  Qed.

  Definition NewMap (t:ty) : expr := AllocMap (zero_val t).
  Theorem NewMap_t t Γ : Γ ⊢ NewMap t : mapT t.
  Proof.
    unfold NewMap.
    repeat econstructor.
    apply zero_val_ty.
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

  Theorem context_extension Γ (t: ty) e :
      Γ ⊢ e : t ->
      forall Γ', (forall x t0, Γ x = Some t0 -> Γ' x = Some t0) ->
      Γ' ⊢ e : t
    with val_context_extension Γ (t: ty) v :
        Γ ⊢v v : t ->
        forall Γ', (forall x t0, Γ x = Some t0 -> Γ' x = Some t0) ->
        Γ' ⊢v v : t.
  Proof.
    - inversion 1; subst; try solve [ (repeat econstructor); eauto ].
    - inversion 1; subst; try solve [ (repeat econstructor); eauto ].
  Qed.

  Theorem empty_context_to_any e t :
    ∅ ⊢ e : t ->
    forall Γ, Γ ⊢ e : t.
  Proof.
    intros.
    eapply context_extension; eauto.
    inversion 1.
  Qed.

  Theorem empty_context_to_any_val v t :
    ∅ ⊢v v : t ->
    forall Γ, Γ ⊢v v : t.
  Proof.
    intros.
    eapply val_context_extension; eauto.
    inversion 1.
  Qed.

  Theorem rec_expr_hasTy_eq t1 t2 Γ Γ' f x e :
    Γ' = (<[f := arrowT t1 t2]> $ <[x := t1]> $ Γ) ->
    Γ' ⊢ e : t2 ->
    Γ ⊢ Rec f x e : arrowT t1 t2.
  Proof.
    intros; subst; eauto.
  Qed.

  Theorem struct_offset_op_hasTy_eq Γ e1 (v: Z) ts ts' :
      Γ ⊢ e1 : structRefT ts ->
      ts' = skipn (Z.to_nat v) ts ->
      Γ ⊢ BinOp OffsetOp e1 #v : structRefT ts'.
  Proof.
    intros; subst; eauto.
  Qed.

  Theorem hasTy_ty_congruence v t1 t2 :
    ∅ ⊢v v : t1 ->
    t1 = t2 ->
    ∅ ⊢v v : t2.
  Proof.
    intros ? ->; auto.
  Qed.

  Theorem Panic_unit_t Γ s : Γ ⊢ Panic s : unitT.
  Proof.
    econstructor.
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
Notation "⊢ e : A" := (val_hasTy ∅ e%V A%ht) (at level 90, e at next level, A at next level) : heap_types.

Theorem insert_anon t : (<[BAnon := t]> : Ctx -> Ctx) = (fun Γ => Γ).
Proof.
  reflexivity.
Qed.

Hint Resolve empty_context_to_any empty_context_to_any_val : types.
Hint Resolve NewMap_t : types.
Hint Resolve hasTy_ty_congruence : types.
Hint Constructors expr_hasTy : types.
Hint Constructors val_hasTy : types.
Hint Constructors base_lit_hasTy : types.
(* note that this has to be after [Hint Constructors expr_hasTy] to get higher
priority than Panic_hasTy *)
Hint Resolve Panic_unit_t : types.
Hint Resolve zero_val_ty : types.

Local Ltac simp := unfold For; rewrite ?insert_anon.
Ltac type_step :=
  match goal with
  | [ |- expr_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- val_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ solve [eauto with types] | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ | solve [eauto with types] ]
  | [ |- expr_hasTy _ (Rec _ (annot_e (annot _ ?t)) _) (arrowT _ _) ] => eapply (rec_expr_hasTy_eq t)
  | [ |- expr_hasTy _ (Rec _ _ _) (arrowT _ _) ] => eapply rec_expr_hasTy_eq
  | [ |- expr_hasTy _ _ _ ] => econstructor
  | [ |- val_hasTy _ _ _ ] => econstructor
  | [ |- base_lit_hasTy _ _ ] =>  econstructor
  end; simp.

Ltac typecheck :=
  intros;
  repeat (type_step; try match goal with
                         | [ |- _ = _ ] => reflexivity
                         end).

Module test.
Section go_lang.
  Context `{ext_ty: ext_types}.
  Local Open Scope heap_types.
  Theorem panic_test Γ : Γ ⊢ (Panic "";; #())%E : unitT.
  Proof.
    typecheck.
  Qed.
End go_lang.
End test.
