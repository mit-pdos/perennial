From Perennial.goose_lang Require Import lang notation map.

Class val_types :=
  { ext_tys: Type; }.

Section val_types.
  Context {val_tys: val_types}.
  Inductive base_ty :=
  | uint64BT
  | uint32BT
  | byteBT
  | boolBT
  | unitBT
  | stringBT.

  Inductive ty :=
  | baseT (t:base_ty)
  | prodT (t1 t2: ty)
  | sumT (t1 t2: ty)
  | arrowT (t1 t2: ty)
  | arrayT (t: ty)
  | structRefT (ts: list ty)
  (* mapValT vt = vt + (uint64 * vt * mapValT vt) *)
  | mapValT (vt: ty) (* keys are always uint64, for now *)
  | extT (x: ext_tys)
  .
  Definition uint64T := baseT uint64BT.
  Definition uint32T := baseT uint32BT.
  Definition byteT   := baseT byteBT.
  Definition boolT   := baseT boolBT.
  Definition unitT   := baseT unitBT.
  Definition stringT := baseT stringBT.
  Definition u8T := byteT.

  (* for backwards compatibility; need a sound plan for dealing with recursive
  structs *)
  Definition anyT : ty := unitT.

  Definition refT (t:ty) : ty := structRefT [t].
  Definition mapT (vt:ty) : ty := refT (mapValT vt).

  Definition Ctx := string -> option ty.
  Global Instance empty_ctx : Empty Ctx := fun _ => None.
  Global Instance ctx_insert : Insert binder ty Ctx.
  Proof using Type.
    hnf.
    exact (fun b t => match b with
                   | BNamed x => fun Γ =>
                                  fun x' => if String.eqb x x'
                                         then Some t
                                         else Γ x'
                   | BAnon => fun Γ => Γ
                   end).
  Defined.
  Global Instance ctx_lookup : Lookup string ty Ctx := fun x Γ => Γ x.
End val_types.

Infix "*" := prodT : heap_type.
Infix "->" := arrowT : heap_type.

Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).
Reserved Notation "Γ '⊢v' v : A" (at level 74, v, A at next level).

Class ext_types (ext:ext_op) :=
  { val_tys :> val_types;
    val_ty_def : ext_tys -> ext_val;
    get_ext_tys: external -> ty * ty; (* the argument type and return type *)
  }.

Section goose_lang.
  Context `{ext_ty: ext_types}.

  Definition ShiftL (t:ty) (e1: expr) (e2: expr): expr :=
    match t with
    | baseT uint64BT => to_u64 e1 ≪ to_u64 e2
    | baseT uint32BT => to_u32 e1 ≪ to_u32 e2
    | baseT byteBT => to_u8 e1 ≪ to_u8 e2
    | _ => #()
    end.

  Definition ShiftR (t:ty) (e1: expr) (e2: expr): expr :=
    match t with
    | baseT uint64BT => to_u64 e1 ≫ to_u64 e2
    | baseT uint32BT => to_u32 e1 ≫ to_u32 e2
    | baseT byteBT => to_u8 e1 ≫ to_u8 e2
    | _ => #()
    end.

  Fixpoint zero_val (t:ty) : val :=
    match t with
    | baseT uint64BT => #0
    | baseT uint32BT => #(U32 0)
    | baseT byteBT => #(U8 0)
    | baseT boolBT => #false
    | baseT unitBT => #()
    | baseT stringT => #(str"")
    | mapValT vt => MapNilV (zero_val vt)
    | prodT t1 t2 => (zero_val t1, zero_val t2)
    | sumT t1 t2 => InjLV (zero_val t1)
    | arrowT t1 t2 => λ: <>, zero_val t2
    | arrayT t => #null
    | structRefT ts => #null
    | extT x => ExtV (val_ty_def x)
    end.

  Fixpoint ty_size (t:ty) : Z :=
    match t with
    | prodT t1 t2 => ty_size t1 + ty_size t2
    | extT x => 1 (* all external values are base literals *)
    | baseT unitT => 1
    | _ => 1
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
  | loc_null_hasTy t : base_lit_hasTy (LitLoc null) (arrayT t)
  | structRef_null_hasTy ts : base_lit_hasTy (LitLoc null) (structRefT ts)
  .

  Theorem array_null_hasTy t : base_lit_hasTy (LitLoc null) (refT t).
  Proof.
    apply structRef_null_hasTy.
  Qed.

  Definition bin_op_ty (op:bin_op) (t:ty) : option (ty * ty * ty) :=
    match op with
    | PlusOp | MinusOp | MultOp | QuotOp | RemOp
    | ShiftLOp | ShiftROp | OrOp | AndOp => Some (t, t, t)
    | LtOp | LeOp => Some (t, t, boolT)
    | _ => None
    end.

  Definition un_op_ty (op:un_op) : option (ty * ty) :=
    match op with
    | NegOp => Some (boolT, boolT)
    | _ => None
    end.

  Definition is_intTy (t: ty) : bool :=
    match t with
    | baseT uint64BT => true
    | baseT uint32BT => true
    | baseT byteBT => true
    | _ => false
    end.

  Definition is_byteTy (t: ty) : bool :=
    match t with
    | baseT byteBT => true
    | _ => false
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
  | arbitrary_int_expr_hasTy :
      Γ ⊢ ArbitraryInt : uint64T
  | fork_hasTy e t :
      Γ ⊢ e : t ->
      Γ ⊢ Fork e : unitT
  | cast_u64_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt64Op e1 : uint64T
  | cast_u32_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt32Op e1 : uint32T
  | cast_u8_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp ToUInt8Op e1 : byteT
  | cast_string_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_byteTy t = true ->
      Γ ⊢ UnOp ToStringOp e1 : stringT
  | un_op_hasTy op e1 t1 t :
      un_op_ty op = Some (t1, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ UnOp op e1 : t
  | offset_op_hasTy e1 e2 k t :
      Γ ⊢ e1 : arrayT t ->
      Γ ⊢ e2 : uint64T ->
      Γ ⊢ BinOp (OffsetOp k) e1 e2 : arrayT t
  | struct_offset_op_hasTy e1 (v: Z) ts :
      Γ ⊢ e1 : structRefT ts ->
      Γ ⊢ BinOp (OffsetOp 1) e1 #v : structRefT (skipn (Z.to_nat v) ts)
  | struct_offset_op_collapse_hasTy e1 (v1 v2: Z) k ts :
      Γ ⊢ BinOp (OffsetOp k) (BinOp (OffsetOp k) e1 #v1) #v2 : structRefT ts ->
      Γ ⊢ BinOp (OffsetOp k) e1 #(v1 + v2) : structRefT ts
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
  | mapNil_hasTy def vt :
      Γ ⊢ def : vt ->
      Γ ⊢ InjL def : mapValT vt
  | mapCons_hasTy k v vt m :
      Γ ⊢ k : uint64T ->
      Γ ⊢ v : vt ->
      Γ ⊢ m : mapValT vt ->
      Γ ⊢ InjR (Pair (Pair k v) m) : mapValT vt
  | case_map_hasTy cond e1 e2 vt t :
      Γ ⊢ cond : mapValT vt ->
      Γ ⊢ e1 : arrowT vt t ->
      Γ ⊢ e2 : arrowT (prodT (prodT uint64T vt ) (mapValT vt)) t ->
      Γ ⊢ Case cond e1 e2 : t
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
  (* TODO: extend to handle structs *)
  | alloc_hasTy n v t :
      Γ ⊢ n : uint64T ->
      Γ ⊢ v : t ->
      Γ ⊢ AllocN n v : arrayT t
  | load_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ Load l : t
  | prepare_write_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ PrepareWrite l : unitT
  | finish_store_hasTy l v t :
      Γ ⊢ l : refT t ->
      Γ ⊢ v : t ->
      Γ ⊢ FinishStore l v : unitT
  | start_read_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ StartRead l : t
  | finish_read_hasTy l t :
      Γ ⊢ l : refT t ->
      Γ ⊢ FinishRead l : unitT
  | cmpxchg_hasTy l v1 v2 t :
      Γ ⊢ l : refT t ->
      Γ ⊢ v1 : t ->
      Γ ⊢ v2 : t ->
      Γ ⊢ CmpXchg l v1 v2 : prodT t boolT
  | external_hasTy op e t1 t2 :
      get_ext_tys op = (t1, t2) ->
      Γ ⊢ e : t1 ->
      Γ ⊢ ExternalOp op e : t2
  | struct_weaken_hasTy e ts1 ts2 :
      Γ ⊢ e : structRefT (ts1 ++ ts2) ->
      Γ ⊢ e : structRefT ts1
  | array_ref_hasTy e t :
      Γ ⊢ e : arrayT t ->
      Γ ⊢ e : refT t
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
  | mapNilV_hasTy v t :
      Γ ⊢v v : t ->
      Γ ⊢v MapNilV v : mapValT t
  | ext_def_hasTy x :
      Γ ⊢v (ExtV (val_ty_def x)) : extT x
  where "Γ ⊢v v : A" := (val_hasTy Γ v A)
  .

  Theorem load_array_hasTy Γ l t :
      Γ ⊢ l : arrayT t ->
      Γ ⊢ Load l : t.
  Proof.
    intros.
    apply load_hasTy.
    apply array_ref_hasTy; auto.
  Qed.

  Theorem store_hasTy Γ l v t :
    Γ ⊢ l : refT t ->
    Γ ⊢ v : t ->
    Γ ⊢ Store l v : unitT.
  Proof.
    intros.
    repeat (econstructor; eauto).
  Qed.

  Theorem store_val_hasTy Γ t :
    Γ ⊢v Store : (arrowT (refT t) (arrowT t unitT)).
  Proof.
    intros.
    repeat (econstructor; eauto).
  Qed.

  Theorem store_array_hasTy Γ l v t :
      Γ ⊢ l : arrayT t ->
      Γ ⊢ v : t ->
      Γ ⊢ Store l v : unitT.
  Proof.
    intros.
    eapply store_hasTy; eauto.
    apply array_ref_hasTy; eauto.
  Qed.

  Theorem store_array_val_hasTy Γ t :
      Γ ⊢v Store : (arrowT (arrayT t) (arrowT t unitT)).
  Proof.
    intros.
    econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
    - econstructor; eauto.
      apply array_ref_hasTy.
      econstructor; eauto.
    - econstructor; eauto.
      econstructor; eauto.
      + apply array_ref_hasTy.
        econstructor; eauto.
      + econstructor; eauto.
  Qed.

  Hint Constructors base_lit_hasTy expr_hasTy val_hasTy base_lit_hasTy.

  Theorem ref_hasTy Γ v t :
    Γ ⊢ v : t ->
    Γ ⊢ ref v : refT t.
  Proof.
    eauto.
  Qed.

  Theorem zero_val_ty ty Γ :
    Γ ⊢v zero_val ty : ty.
  Proof.
    generalize dependent Γ.
    induction ty; simpl; eauto.
    destruct t; eauto.
  Qed.

  Definition NewMap (t:ty) : expr := Alloc (zero_val (mapValT t)).
  Theorem NewMap_t t Γ : Γ ⊢ NewMap t : mapT t.
  Proof.
    unfold NewMap, mapT.
    eapply array_ref_hasTy.
    econstructor.
    - repeat econstructor.
    - econstructor.
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
    - inversion 1; subst; solve [ econstructor; eauto ].
    - inversion 1; subst; solve [ econstructor; eauto ].
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
      Γ ⊢ BinOp (OffsetOp 1) e1 #v : structRefT ts'.
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

End goose_lang.

Notation "v :: t" := (annot v t) (only printing) : expr_scope.
Coercion annot_e : type_annot >-> string.

Delimit Scope heap_types with T.
Delimit Scope heap_type with ht.
Bind Scope heap_type with ty.

Notation "Γ ⊢ e : A" := (expr_hasTy Γ%ht e A%ht) : heap_types.
Notation "Γ ⊢v v : A" := (val_hasTy Γ%ht v A%ht) : heap_types.
Notation "⊢ v : A" := (base_lit_hasTy v%V A%ht) (at level 90, only printing) : heap_types.
Notation "⊢ e : A" := (val_hasTy ∅ e%V A%ht) (at level 90, e at next level, A at next level) : heap_types.

Theorem insert_anon `{ext_ty: ext_types} t : (<[BAnon := t]> : Ctx -> Ctx) = (fun Γ => Γ).
Proof.
  reflexivity.
Qed.

Hint Resolve empty_context_to_any empty_context_to_any_val : types.
Hint Resolve NewMap_t : types.
Hint Resolve hasTy_ty_congruence : types.
Hint Constructors expr_hasTy : types.
Hint Constructors val_hasTy : types.
Hint Constructors base_lit_hasTy : types.
Remove Hints array_ref_hasTy : types.
(* note that this has to be after [Hint Constructors expr_hasTy] to get higher
priority than Panic_hasTy *)
Hint Resolve Panic_unit_t : types.
Hint Resolve zero_val_ty : types.
Hint Resolve var_hasTy : types.
Hint Resolve ref_hasTy load_array_hasTy store_array_hasTy array_null_hasTy : types.
Hint Resolve store_val_hasTy store_array_val_hasTy : types.

Hint Extern 1 (expr_hasTy _ _ _) => apply var_hasTy; reflexivity : types.

Local Ltac simp := unfold For; rewrite ?insert_anon.
Ltac _type_step :=
  match goal with
  | [ |- expr_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- val_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- expr_hasTy _ (Store _ _) _ ] => eapply store_array_hasTy; [ solve [eauto with types] | ]
  | [ |- expr_hasTy _ (Load _) _ ] => eapply load_array_hasTy; [ solve [eauto with types] ]
  | [ |- expr_hasTy _ (ref _) _ ] => eapply ref_hasTy
  | [ |- expr_hasTy _ (UnOp ToUInt64Op _) _ ] => eapply cast_u64_op_hasTy
  | [ |- expr_hasTy _ (UnOp ToUInt32Op _) _ ] => eapply cast_u32_op_hasTy
  | [ |- expr_hasTy _ (UnOp ToUInt8Op _) _ ] => eapply cast_u8_op_hasTy
  | [ |- expr_hasTy _ (UnOp ToStringOp _) _ ] => eapply cast_string_op_hasTy
  | [ |- expr_hasTy _ (BinOp _ _ _) uint32T ] => eapply bin_op_32_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp _ _ _) uint64T ] => eapply bin_op_64_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp _ _ _) uint32T ] => eapply bin_op_32_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ solve [eauto with types] | | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ | solve [eauto with types] | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply bin_op_32_hasTy; [ reflexivity | solve [eauto with types] | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply bin_op_32_hasTy; [ reflexivity | | solve [eauto with types] ]
  | [ |- expr_hasTy _ (Rec _ (annot_e (annot _ ?t)) _) (arrowT _ _) ] => eapply (rec_expr_hasTy_eq t)
  | [ |- expr_hasTy _ (Rec _ _ _) (arrowT _ _) ] => eapply rec_expr_hasTy_eq
  | [ |- expr_hasTy _ _ _ ] => econstructor
  | [ |- val_hasTy _ _ _ ] => econstructor
  | [ |- base_lit_hasTy _ _ ] =>  econstructor
  end; simp.

Ltac type_step := _type_step;
                  try lazymatch goal with
                      | [ |- _ = _ ] => reflexivity
                      end.

Ltac typecheck :=
  intros;
  repeat type_step;
  try lazymatch goal with
      | [ |- _ = _ ] => reflexivity
      end.

(* the first notation is a location offset in the model (a pure function over
locations) while the second is a GooseLang expression; the second evaluates to
the first according to the GooseLang semantics. *)
Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ ty_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (ty_size t)) e1%E e2%E) : expr_scope .

Section goose_lang.
  Context `{ext_ty: ext_types}.
  Local Open Scope heap_types.
  Theorem MapGet_t Γ vt : Γ ⊢ MapGet : (mapT vt -> uint64T -> vt * boolT).
  Proof.
    typecheck.
  Qed.

  Theorem MapInsert_t Γ vt : Γ ⊢v MapInsert : (mapT vt -> uint64T -> vt -> unitT).
  Proof.
    type_step.
    type_step.
    type_step.
    eapply store_hasTy; typecheck.
  Qed.

  Theorem mapGetDef_t Γ vt : Γ ⊢ mapGetDef : (mapValT vt -> vt).
  Proof.
    typecheck.
  Qed.

  Hint Resolve mapGetDef_t : types.

  Theorem MapClear_t Γ vt : Γ ⊢ MapClear : (mapT vt -> unitT).
  Proof.
    type_step.
    type_step.
    type_step.
    { typecheck. }
    type_step.
    eapply store_hasTy; typecheck.
  Qed.

  Theorem MapIter_t vt Γ : Γ ⊢ MapIter : (mapT vt -> (uint64T -> vt -> unitT) -> unitT).
  Proof.
    typecheck.
  Qed.
End goose_lang.

Opaque MapGet MapInsert MapClear MapIter.
Hint Resolve MapGet_t MapInsert_t MapClear_t MapIter_t : types.

Module test.
Section goose_lang.
  Context `{ext_ty: ext_types}.
  Local Open Scope heap_types.
  Theorem panic_test Γ : Γ ⊢ (Panic "";; #())%E : unitT.
  Proof.
    typecheck.
  Qed.
End goose_lang.
End test.
