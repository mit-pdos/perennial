From stdpp Require Import gmap.
From Perennial.goose_lang Require Import lang notation.
From Perennial.goose_lang.lib Require Import lock.impl channel.impl map.impl list.impl.

Set Default Proof Using "Type".

Class val_types :=
  { ext_tys: Type; }.

Section val_types.
  Context {val_tys: val_types}.
  Inductive base_ty : Set :=
  | uint64BT
  | uint32BT
  | byteBT
  | boolBT
  | unitBT
  | stringBT.

  Inductive ty :=
  | baseT (t:base_ty)
  | prodT (t1 t2: ty)
  | listT (t1: ty) (* for refinement proofs only *)
  | sumT (t1 t2: ty)
  | arrowT (t1 t2: ty)
  | arrayT (t: ty)
  (* opaque pointer type, pointee unknown *)
  | ptrT
  (* pointer to *flattened* data (the list should usually not contain prodT or
  unitBT) *)
  | structRefT (ts: list ty)
  (* mapValT vt = vt + (uint64 * vt * mapValT vt) *)
  | mapValT (kt:ty) (vt: ty)
  | chanValT (vt: ty)
  | extT (x: ext_tys)
  (* propehy variable *)
  | prophT
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

  Definition Ctx := gmap string ty.
  Global Instance ctx_insert : Insert binder ty Ctx.
  Proof.
    hnf.
    exact (fun b t => match b with
                   | BNamed x => fun Γ => <[ x := t ]> Γ
                   | BAnon => fun Γ => Γ
                   end).
  Defined.
  (*
  Global Instance ctx_lookup : Lookup string ty Ctx := fun x Γ => Γ x.
   *)
End val_types.

Declare Scope heap_type.
Infix "*" := prodT : heap_type.
Infix "->" := arrowT : heap_type.

Reserved Notation "Γ ⊢ e : A" (at level 74, e, A at next level).
Reserved Notation "Γ '⊢v' v : A" (at level 74, v, A at next level).

Class ext_types (ext:ffi_syntax) :=
  { #[global] val_tys :: val_types;
    (* the argument type and return type *)
    get_ext_tys: val -> ty * ty -> Prop;
  }.

Section goose_lang.
  Context `{ext_ty: ext_types}.

  Fixpoint zero_val (t:ty) : val :=
    match t with
    | baseT uint64BT => #0
    | baseT uint32BT => #(W32 0)
    | baseT byteBT => #(W8 0)
    | baseT boolBT => #false
    | baseT unitBT => #()
    | baseT stringBT => #(str"")
    | mapValT kt vt => MapNilV (zero_val vt)
    | chanValT vt => ChannelClosedV (zero_val vt)
    | prodT t1 t2 => (zero_val t1, zero_val t2)
    | listT t => InjLV (LitV LitUnit)
    | sumT t1 t2 => InjLV (zero_val t1)
    | arrowT t1 t2 => (λ: <>, Val (zero_val t2))%V
    | arrayT t => #null
    | structRefT _ | ptrT => #null
    | extT _ | prophT => #() (* dummy value of wrong type *)
    end.

  Lemma zero_prod_val t1 t2 :
    zero_val (prodT t1 t2) = (zero_val t1, zero_val t2)%V.
  Proof. reflexivity. Qed.

  Fixpoint storable (t:ty): Prop :=
    match t with
    | listT _ => False
    | prodT t1 t2 => storable t1 /\ storable t2
    | _ => True
    end.

  Fixpoint has_zero (t:ty): Prop :=
    match t with
    | baseT _ => True
    (*
    | mapValT t => has_zero t
    *)
    | mapValT t1 t2 => False
    | chanValT t => False
    | prodT t1 t2 => has_zero t1 ∧ has_zero t2
    | listT t => has_zero t
    | sumT t1 t2 => has_zero t1
    | arrowT _ t2 => has_zero t2
    | arrayT _ => True
    | structRefT _ => True
    | ptrT => True
    | extT _ => False
    | prophT => False
    end.

  (* TODO: listT size is not well defined, but it shouldn't be going in structs anyway *)
  Fixpoint ty_size (t:ty) : Z :=
    match t with
    | prodT t1 t2 => ty_size t1 + ty_size t2
    | extT x => 1 (* all external values are base literals *)
    | baseT unitBT => 0
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
  | ptr_null_hasTy : base_lit_hasTy (LitLoc null) ptrT
  .

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

  Definition is_unboxed_baseTy (t: ty) : bool :=
    match t with
    | baseT _ => true
    | arrayT _ => true
    | structRefT _ => true
    | ptrT => false (* seems to only affect the logrel *)
    | _ => false
    end.

  Definition is_unboxedTy (t: ty) : bool :=
    match t with
    | baseT _ => true
    | arrayT _ => true
    | structRefT _ => true
    | ptrT => false (* seems to only affect the logrel *)
    | sumT t1 t2 => is_unboxed_baseTy t1 && is_unboxed_baseTy t2
    | _ => false
    end.

  Fixpoint is_comparableTy (t: ty) : bool :=
    match t with
    | baseT _ => true
    | prodT t1 t2 => is_comparableTy t1 && is_comparableTy t2
    | sumT t1 t2 => is_comparableTy t1 && is_comparableTy t2
    | arrayT _ => true
    | structRefT _ => true
    | ptrT => false (* seems to only affect the logrel *)
    | _ => false
    end.

  Lemma unboxed_baseTy_unboxed (t1: ty):
    is_unboxed_baseTy t1 = true →
    is_unboxedTy t1 = true.
  Proof. destruct t1 => //=. Qed.

  Lemma unboxedTy_comparable (t: ty):
    is_unboxedTy t = true →
    is_comparableTy t = true.
  Proof.
    induction t => //=. intros (?&?)%andb_prop.
    rewrite IHt1 //=; eauto using unboxed_baseTy_unboxed.
  Qed.

  Fixpoint flatten_ty (t: ty) : list ty :=
    match t with
    | prodT t1 t2 => flatten_ty t1 ++ flatten_ty t2
    | baseT unitBT => []
    | _ => [t]
    end.

  Definition refT (t:ty) : ty := structRefT (flatten_ty t).

  Theorem array_null_hasTy t : base_lit_hasTy (LitLoc null) (refT t).
  Proof.
    apply structRef_null_hasTy.
  Qed.

  Theorem ty_size_ge_0 : forall t, (0 <= ty_size t)%Z.
  Proof.
    induction t; simpl; try lia.
    destruct t; lia.
  Qed.

  Theorem ty_size_length t : Z.to_nat (ty_size t) = length (flatten_ty t).
  Proof.
    induction t; simpl; auto.
    - destruct t; simpl; auto.
    - pose proof (ty_size_ge_0 t1).
      pose proof (ty_size_ge_0 t2).
      rewrite length_app; auto.
      rewrite Z2Nat.inj_add; lia.
  Qed.

  Inductive expr_hasTy (Γ: Ctx) : expr -> ty -> Prop :=

  (** structural rules *)
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
  | fork_hasTy e t :
      Γ ⊢ e : t ->
      Γ ⊢ Fork e : unitT

  (** control flow *)
  | if_hasTy cond e1 e2 t :
      Γ ⊢ cond : boolT ->
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      Γ ⊢ If cond e1 e2 : t

  (** primitives operations *)
  | panic_expr_hasTy msg t :
      Γ ⊢ Panic msg : t
  | arbitrary_int_expr_hasTy :
      Γ ⊢ ArbitraryInt : uint64T
  | cast_u64_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp UToW64Op e1 : uint64T
  | cast_s64_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp SToW64Op e1 : uint64T
  | cast_u32_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp UToW32Op e1 : uint32T
  | cast_s32_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp SToW32Op e1 : uint32T
  | cast_u8_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp UToW8Op e1 : byteT
  | cast_s8_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_intTy t = true ->
      Γ ⊢ UnOp SToW8Op e1 : byteT
  | cast_string_op_hasTy e1 t :
      Γ ⊢ e1 : t ->
      is_byteTy t = true ->
      Γ ⊢ UnOp ToStringOp e1 : stringT
  | un_op_hasTy op e1 t1 t :
      un_op_ty op = Some (t1, t) ->
      Γ ⊢ e1 : t1 ->
      Γ ⊢ UnOp op e1 : t
  | eq_op_hasTy e1 e2 t :
      Γ ⊢ e1 : t ->
      Γ ⊢ e2 : t ->
      is_comparableTy t = true ->
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

  (** data *)
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
  | cons_hasTy ehd etl t :
      Γ ⊢  ehd : t ->
      Γ ⊢  etl : listT t ->
      Γ ⊢  ListCons ehd etl : listT t
  | listmatch_hasTy el nilfun consfun tl tret :
      Γ ⊢ el : listT tl ->
      Γ ⊢ nilfun : arrowT unitT tret ->
      Γ ⊢ consfun : arrowT (prodT tl (listT tl)) tret ->
      Γ ⊢ ListMatch el nilfun consfun : tret
  | mapNil_hasTy def kt vt :
      Γ ⊢ def : vt ->
      Γ ⊢ InjL def : mapValT kt vt
  | mapCons_hasTy k v kt vt m :
      Γ ⊢ k : kt ->
      Γ ⊢ v : vt ->
      Γ ⊢ m : mapValT kt vt ->
      Γ ⊢ InjR (Pair (Pair k v) m) : mapValT kt vt
  | case_map_hasTy cond e1 e2 kt vt t :
      Γ ⊢ cond : mapValT kt vt ->
      Γ ⊢ e1 : arrowT vt t ->
      Γ ⊢ e2 : arrowT (prodT (prodT kt vt ) (mapValT kt vt)) t ->
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

  (** pointers *)
  | alloc_hasTy n v t :
      storable t →
      Γ ⊢ n : uint64T ->
      Γ ⊢ v : t ->
      Γ ⊢ AllocN n v : arrayT t
  | offset_op_hasTy e1 e2 t :
      Γ ⊢ e1 : arrayT t ->
      Γ ⊢ e2 : uint64T ->
      Γ ⊢ BinOp (OffsetOp (ty_size t)) e1 e2 : arrayT t
  | array_struct_hasTy e t :
      Γ ⊢ e : arrayT t ->
      Γ ⊢ e : structRefT (flatten_ty t)
  | struct_offset_op_hasTy e1 (k: Z) ts :
      0 ≤ k →
      Z.to_nat k < length ts →
      Γ ⊢ e1 : structRefT ts ->
      Γ ⊢ BinOp (OffsetOp k) e1 #1 : structRefT (drop (Z.to_nat k) ts)
  | load_hasTy l t ts :
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ Load l : t
  | store_hasTy l v t ts :
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ v : t ->
      Γ ⊢ Store l v : unitT
  | start_read_hasTy l t ts :
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ StartRead l : t
  | finish_read_hasTy l t ts :
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ FinishRead l : unitT
  | cmpxchg_hasTy l v1 v2 t ts :
      is_unboxedTy t = true ->
      Γ ⊢ l : structRefT (t::ts) ->
      Γ ⊢ v1 : t ->
      Γ ⊢ v2 : t ->
      Γ ⊢ CmpXchg l v1 v2 : prodT t boolT
  (** I/O *)
  | input_hasTy sel :
      Γ ⊢ sel : uint64T ->
      Γ ⊢ Input sel : uint64T
  | output_hasTy v :
      Γ ⊢ v : uint64T ->
      Γ ⊢ Output v : unitT

  (** externals *)
  | external_hasTy e earg t1 t2 :
      get_ext_tys e (t1, t2) ->
      Γ ⊢ earg : t1 ->
      Γ ⊢ e earg : t2

  where "Γ ⊢ e : A" := (expr_hasTy Γ e A)

  with val_hasTy (Γ: Ctx) : val -> ty -> Prop :=
  | val_base_lit_hasTy v t :
      base_lit_hasTy v t ->
      Γ ⊢v (LitV v) : t
  | val_pair_hasTy v1 v2 t1 t2 :
      Γ ⊢v v1 : t1 ->
      Γ ⊢v v2 : t2 ->
      Γ ⊢v PairV v1 v2 : prodT t1 t2
  | val_nil_hasTy t :
      Γ ⊢v ListNilV : listT t
  | val_cons_hasTy vhd vtl t :
      Γ ⊢v vhd : t ->
      Γ ⊢v vtl : listT t ->
      Γ ⊢v ListConsV vhd vtl : listT t
  | val_injL_hasTy v1 t1 t2 :
      Γ ⊢v v1 : t1 ->
      Γ ⊢v InjLV v1 : sumT t1 t2
  | val_injR_hasTy v2 t1 t2 :
      Γ ⊢v v2 : t2 ->
      Γ ⊢v InjRV v2 : sumT t1 t2
  | rec_val_hasTy f x e t1 t2 :
      (<[f := arrowT t1 t2]> $ <[x := t1]> $ ∅) ⊢ e : t2 ->
      Γ ⊢v RecV f x e : arrowT t1 t2
  | mapNilV_hasTy v kt vt :
      Γ ⊢v v : vt ->
      Γ ⊢v MapNilV v : mapValT kt vt
  where "Γ ⊢v v : A" := (val_hasTy Γ v A)
  .

  Hint Constructors expr_hasTy val_hasTy base_lit_hasTy : core.

  Theorem zero_val_ty t Γ :
    has_zero t ->
    Γ ⊢v zero_val t : t.
  Proof.
    revert Γ.
    induction t; simpl; eauto; intros; intuition eauto.
    destruct t; eauto.
  Qed.

  Lemma extend_context_add:
    ∀ Γ Γ' : Ctx,
      (∀ (x : string) (t0 : ty), Γ !! x = Some t0 → Γ' !! x = Some t0)
      → ∀ (x : binder) (t: ty) (x0 : string) (t0 : ty),
        (<[x:=t]> Γ) !! x0 = Some t0
        → (<[x:=t]> Γ') !! x0 = Some t0.
  Proof.
    intros Γ Γ' Heq f t x t0 HΓ.
    unfold insert, ctx_insert in *.
    destruct f; eauto.
    destruct (s =? x)%string eqn:Heq_s.
    - apply String.eqb_eq in Heq_s. subst.
      move: HΓ. rewrite ?lookup_insert_eq //=.
    - apply String.eqb_neq in Heq_s.
      move: HΓ. rewrite ?lookup_insert_ne //=; eauto.
  Qed.

  Hint Resolve extend_context_add : core.

  Theorem context_extension Γ (t: ty) e :
      Γ ⊢ e : t ->
      forall Γ', (forall x t0, Γ !! x = Some t0 -> Γ' !! x = Some t0) ->
      Γ' ⊢ e : t
    with val_context_extension Γ (t: ty) v :
        Γ ⊢v v : t ->
        forall Γ', (forall x t0, Γ !! x = Some t0 -> Γ' !! x = Some t0) ->
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

  Theorem ref_hasTy t Γ ts e :
    storable t ->
    Γ ⊢ e : t ->
    ts = flatten_ty t ->
    Γ ⊢ ref e : structRefT ts.
  Proof.
    intros ? He ->.
    eapply array_struct_hasTy.
    eauto.
  Qed.

  Definition mapT (vt:ty) : ty := ptrT.

  (* A thunk that creates a map. *)
  Definition NewMap (kt vt:ty) : val :=
    λ: <>, Alloc (zero_val (mapValT kt vt)).
  (*
  Theorem NewMap_t t Γ : has_zero t -> Γ ⊢ NewMap t : mapT t.
  Proof.
    intros Hzero.
    unfold NewMap, mapT.
    eapply (ref_hasTy (mapValT t)); eauto.
    constructor.
    apply zero_val_ty; eauto.
  Qed.
  *)

  Definition chanT (vt:ty) : ty := (prodT ptrT ptrT).

  Definition NewChan (t:ty) : val :=
  λ: "cap",
    let: "chanref" := Alloc (InjR (Var "cap", Var "cap", ChannelNilV (zero_val t))) in
    let: "lock" := lock.new #() in
    (InjR (Var "chanref", Var "lock"))
  .
End goose_lang.

Declare Scope heap_types.
Delimit Scope heap_types with T.
Delimit Scope heap_type with ht.
Bind Scope heap_type with ty.

Arguments zero_val : simpl never.

Notation "Γ ⊢ e : A" := (expr_hasTy Γ%ht e A%ht) : heap_types.
Notation "Γ ⊢v v : A" := (val_hasTy Γ%ht v A%ht) : heap_types.

Theorem insert_anon `{ext_ty: ext_types} t : (<[BAnon := t]> : Ctx -> Ctx) = (fun Γ => Γ).
Proof.
  reflexivity.
Qed.

#[global]
Hint Resolve empty_context_to_any empty_context_to_any_val : types.
(*
Hint Resolve NewMap_t : types.
*)
#[global]
Hint Resolve hasTy_ty_congruence : types.
#[global]
Hint Constructors expr_hasTy : types.
#[global]
Hint Constructors val_hasTy : types.
#[global]
Hint Constructors base_lit_hasTy : types.
(* note that this has to be after [Hint Constructors expr_hasTy] to get higher
priority than Panic_hasTy *)
#[global]
Hint Resolve Panic_unit_t : types.
#[global]
Hint Resolve zero_val_ty : types.
#[global]
Hint Resolve var_hasTy : types.
#[global]
Hint Resolve array_null_hasTy : types.

#[global]
Hint Extern 1 (expr_hasTy _ _ _) => apply var_hasTy; reflexivity : types.

Local Ltac simp := rewrite ?insert_anon.
Ltac _type_step :=
  match goal with
  | [ |- expr_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- val_hasTy _ _ _ ] => solve [eauto with types]
  | [ |- expr_hasTy _ (UnOp UToW64Op _) _ ] => eapply cast_u64_op_hasTy
  | [ |- expr_hasTy _ (UnOp SToW64Op _) _ ] => eapply cast_s64_op_hasTy
  | [ |- expr_hasTy _ (UnOp UToW32Op _) _ ] => eapply cast_u32_op_hasTy
  | [ |- expr_hasTy _ (UnOp SToW32Op _) _ ] => eapply cast_s32_op_hasTy
  | [ |- expr_hasTy _ (UnOp UToW8Op _) _ ] => eapply cast_u8_op_hasTy
  | [ |- expr_hasTy _ (UnOp SToW8Op _) _ ] => eapply cast_s8_op_hasTy
  | [ |- expr_hasTy _ (UnOp ToStringOp _) _ ] => eapply cast_string_op_hasTy
  | [ |- expr_hasTy _ (BinOp _ _ _) uint32T ] => eapply bin_op_32_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp _ _ _) uint64T ] => eapply bin_op_64_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp _ _ _) uint32T ] => eapply bin_op_32_hasTy; [ reflexivity | | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ solve [eauto with types] | | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply str_plus_hasTy; [ | solve [eauto with types] | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply bin_op_32_hasTy; [ reflexivity | solve [eauto with types] | ]
  | [ |- expr_hasTy _ (BinOp PlusOp _ _) _ ] => eapply bin_op_32_hasTy; [ reflexivity | | solve [eauto with types] ]
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

(* RJ: These have been the cause of considerate slowdown, so I disabled them.
Hint Extern 1 (has_zero _) => (compute; intuition idtac) : core.
Hint Extern 1 (has_zero _) => (compute; intuition idtac) : val_ty.
*)

(* the first notation is a location offset in the model (a pure function over
locations) while the second is a GooseLang expression; the second evaluates to
the first according to the GooseLang semantics. *)
Reserved Notation "l +ₗ[ t ] z" (at level 50, left associativity, format "l  +ₗ[ t ]  z").
Notation "l +ₗ[ t ] z" := (l +ₗ ty_size t * z) : stdpp_scope .
Notation "e1 +ₗ[ t ] e2" := (BinOp (OffsetOp (ty_size t)) e1%E e2%E) : expr_scope .

Lemma byte_offset_untype `{ext_ty: ext_types} l z :
  l +ₗ[byteT] z = l +ₗ z.
Proof. rewrite Z.mul_1_l. done. Qed.

Lemma loc_add_typed_assoc `{ext_ty: ext_types} {t} l z1 z2 :
  l +ₗ[t] z1 +ₗ[t] z2 = l +ₗ[t] (z1 + z2).
Proof.
  rewrite loc_add_assoc.
  rewrite Z.mul_add_distr_l //.
Qed.
